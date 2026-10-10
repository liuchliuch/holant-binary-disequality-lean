import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBNormalizedPin
import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularPrepare
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseResolved

/-! Actual B-singular preparation in a finite normalized alphabet. The old
original palette is enlarged only by saved actual graphs; its normalized pin
and old normalized phase are literal rows of the resulting native source.
The cycle anchor, traceless binary and isotropic ordinary unary share one basis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBNonisotropicPrepare
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Marked.SupportAtlas Holant.EightVertex.ProductAnchor
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace U
export GlobalCloseCompletionBUnary (palette root root_nonzero)
end U
namespace Pin
export GlobalCloseCompletionBNormalizedPin (normalized Receipt receipt)
end Pin
namespace R
export GlobalCloseCompletionBDenseRepresentatives (family family_finite_eq original normal)
end R
namespace C
export GlobalCloseCompletionSingularCubicCycle (cubic)
export GlobalCloseCompletionSingularCycleReceipt (Receipt produce)
end C
namespace Ph
export GlobalCloseCompletionSingularPhaseBinary
  (diagonal offDiagonal normalization_phase nonsingular offDiagonal_nonzero choose_phase)
end Ph
namespace V
export GlobalCloseCompletionSingularNAND (traceless unary)
end V
namespace Pr
export GlobalCloseCompletionSingularPrepare (pinFirst pinSecond normalization_pin pinFirst_nonzero pin_square)
end Pr
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

private theorem cubic_eq (a b : AlgebraicComplex) :
    GlobalCloseCompletionSingularCubic.symmetric a b=C.cubic a b := by
  funext z
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;>
    simp [GlobalCloseCompletionSingularCubic.symmetric,GlobalCloseCompletionSingularCubic.cubic,
      GlobalCloseCompletionSingularCubic.parity,C.cubic,h0,h1,h2]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

abbrev family (Q : Palette G) := UniversalPairReduction.FiniteFamily.family (GlobalCloseCompletionBNativeCodec.mapped G Q)

theorem family_mono (Q : Palette G) (old : P.family⊆Q.family) : R.family G P⊆R.family G Q := by
  rintro f (⟨g,⟨h,hh,rfl⟩,rfl⟩|rfl)
  · exact Or.inl ⟨_,⟨h,old hh,rfl⟩,rfl⟩
  · exact Or.inr rfl

theorem normalized_member (Q : Palette G) {n : ℕ} (f : Signature (OI.K G) n)
    (retained : (⟨n,f⟩ : AnySignature (OI.K G))∈Q.family) :
    (⟨n,Pin.normalized G f⟩ : AnySignature AlgebraicComplex)∈family G Q := by
  change (⟨n,Pin.normalized G f⟩ : AnySignature AlgebraicComplex)∈
    UniversalPairReduction.FiniteFamily.family (GlobalCloseCompletionBNativeCodec.mapped G Q)
  rw [←R.family_finite_eq G Q]
  exact Or.inl ⟨⟨n,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f⟩,
    ⟨⟨n,f⟩,retained,rfl⟩,rfl⟩

structure Prepared : Type 1 where
  palette : Palette G
  old : P.family⊆palette.family
  anchor : QuaternaryEqualityTerminal.AnchorStep (family G palette)
  edge_one : anchor.edgeScale=1
  binary : Signature (OI.K G) 2
  binary_retained : (⟨2,binary⟩ : AnySignature (OI.K G))∈palette.family
  x : AlgebraicComplex
  y : AlgebraicComplex
  y_nonzero : y≠0
  nonsingular : x^2+y^2≠0
  binary_exact : anchor.basis.action (Pin.normalized G binary)=V.traceless x y
  unary : Signature (OI.K G) 1
  unary_retained : (⟨1,unary⟩ : AnySignature (OI.K G))∈palette.family
  u : AlgebraicComplex
  v : AlgebraicComplex
  u_nonzero : u≠0
  square : v^2= -u^2
  unary_exact : anchor.basis.action (Pin.normalized G unary)=V.unary u v

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (r : GlobalCloseCompletionBDenseEscape.SingularReceipt G P)
variable (q : Signature (OI.K G) 4) (p : Bool)
variable (retained : (⟨4,q⟩ : AnySignature (OI.K G))∈P.family)
variable (full : ∀x,Pin.normalized G q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p)

include torsion N r retained full in
theorem prepared_exists : Nonempty (Prepared G P) := by
  let Q := U.palette G P r
  have oldQ : P.family⊆Q.family := ProgrammeSaturation.retains_old G P (U.root G P r)
    (U.root_nonzero G P r) (by change 0<2; decide) r.actual
  let pin := Pin.receipt G P r
  have qa : Gadget.Realizes (R.family G Q) .disequality (Pin.normalized G q) := by
    apply Gadget.realizes_of_mem
    exact Or.inl ⟨⟨4,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q⟩,
      ⟨⟨4,q⟩,oldQ retained,rfl⟩,rfl⟩
  obtain ⟨A,B,hA,hB,hcubic⟩ := GlobalCloseCompletionSingularSlice.exists_symmetric
    (R.family G Q) (GlobalCloseCompletionBCoordinateRealizes.identity _) (Pin.normalized G q) p full qa
    pin.coefficient pin.nonzero (pin.both_actual G P r)
  rw [cubic_eq] at hcubic
  obtain ⟨cycle⟩ := C.produce (R.family G Q) A B hA hB hcubic
  have positive : 0<N.selected.m := by have := N.selected.range; omega
  let omega := ClosureMarkedDihedral.liftRoot positive N.selected.omega N.selected.primitive
  have different : omega≠1 := by
    intro eq
    have hv : (N.selected.omega : ℂ)=1 := congrArg ClosureMarkedDihedral.inclusion eq
    have hu : N.selected.omega=1 := Units.ext hv
    have hd : N.selected.m∣1 := N.selected.primitive.dvd_of_pow_eq_one 1 (by simp [hu])
    have := Nat.le_of_dvd (by decide : 0<1) hd
    have := N.selected.range
    omega
  obtain ⟨t,ht,hgap⟩ := Ph.choose_phase cycle.r omega different
  have root : Roots N.selected.m t := by
    rcases ht with rfl|rfl
    · exact Roots.one _
    · exact ClosureMarkedDihedral.liftRoot_root positive N.selected.omega N.selected.primitive
  have tn : t≠0 := root.ne_zero positive
  let phase : Phase N.selected.m := ⟨t,root⟩
  let index := HistorySectorNormalized.phaseIndex G P torsion basisB N.selected false phase
  let binary := binarySignature (actualRepresentative P.family torsion index.key)
  have bn : binary≠0 := actualRepresentative_signature_nonzero P.family torsion index.key
  have ba : Gadget.Realizes Q.family .disequality binary :=
    (actualRepresentative_actual P.family torsion index.key).1.mono oldQ
  let W := ProgrammeSaturation.palette G Q ⟨2,binary⟩ bn (by change 0<2; decide) ba
  have oldW : Q.family⊆W.family := ProgrammeSaturation.retains_old G Q ⟨2,binary⟩ bn (by change 0<2; decide) ba
  have normalizedOld : R.family G Q⊆family G W := by
    change R.family G Q⊆UniversalPairReduction.FiniteFamily.family (GlobalCloseCompletionBNativeCodec.mapped G W)
    rw [←R.family_finite_eq G W]
    exact family_mono G Q W oldW
  let anchor : QuaternaryEqualityTerminal.AnchorStep (family G W) :=
    { signature := cycle.output
      basis := cycle.basis
      edgeScale := 1
      vertexScale := cycle.coefficient
      edge_ne_zero := one_ne_zero
      vertex_ne_zero := cycle.coefficient_nonzero hA hB
      actual := cycle.actual.mono normalizedOld
      edge_exact := by simpa only [one_mul] using cycle.edge
      anchor_exact := cycle.normalized }
  let mu := (R.original G P torsion N).multiplier false phase/ClosureBStable.edgeScalar
  have mn : mu≠0 := div_ne_zero ((R.original G P torsion N).multiplier_ne_zero false phase)
    ClosureBStable.edgeScalar_nonzero
  have binaryNormal : Pin.normalized G binary=kernelSignature (scale mu (Holant.Marked.R t)) := by
    change basisB.symm.action (kernelSignature ((R.original G P torsion N).matrix false phase))=_
    rw [transport_signature,R.normal]
    rfl
  refine ⟨⟨W,(fun f hf=>oldW (oldQ hf)),anchor,rfl,binary,?_,Ph.diagonal cycle.r cycle.u mu t,
    Ph.offDiagonal cycle.r cycle.u mu t,
    Ph.offDiagonal_nonzero _ _ _ _ cycle.r_nonzero cycle.u_nonzero mn hgap,
    Ph.nonsingular _ _ _ _ cycle.r_nonzero mn tn cycle.u_square,?_,
    pin.output,oldW pin.retained,Pr.pinFirst cycle.r cycle.u pin.coefficient pin.bit,
    Pr.pinSecond cycle.r cycle.u pin.coefficient pin.bit,
    Pr.pinFirst_nonzero _ _ _ cycle.r_nonzero cycle.u_nonzero pin.nonzero pin.bit,
    Pr.pin_square _ _ _ pin.bit,?_⟩⟩
  · exact ProgrammeSaturation.retains_output G Q ⟨2,binary⟩ bn (by change 0<2; decide) ba
  · change cycle.basis.action (Pin.normalized G binary)=_
    rw [binaryNormal]
    exact Ph.normalization_phase _ _ _ _ cycle.r_nonzero cycle.u_nonzero
  · change cycle.basis.action (Pin.normalized G pin.output)=_
    rw [pin.exact]
    exact Pr.normalization_pin _ _ _ cycle.r_nonzero cycle.u_nonzero pin.bit

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBNonisotropicPrepare
end
