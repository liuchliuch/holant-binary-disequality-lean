import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0NormalizedPin
import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularPrepare
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0DenseCanonical

/-! Actual A0 singular preparation in a finite normalized alphabet. The old
original palette is enlarged only by saved actual graphs; its normalized pin
and old normalized phase are literal rows of the resulting native source.
The cycle anchor, traceless binary and isotropic ordinary unary share one basis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0SingularPrepare
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Marked.SupportAtlas Holant.EightVertex.ProductAnchor
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace U
export GlobalCloseCompletionA0Unary (base palette root root_nonzero old old_base row)
end U
namespace Pin
export GlobalCloseCompletionA0NormalizedPin (normalized Receipt receipt)
end Pin
namespace R
export GlobalCloseCompletionA0Family (family family_eq)
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

abbrev family (Q : Palette G) := UniversalPairReduction.FiniteFamily.family (GlobalCloseCompletionA0NativeCodec.mapped G Q)

theorem family_mono (Q : Palette G) (old : P.family⊆Q.family) : R.family G P⊆R.family G Q := by
  rintro f (⟨g,⟨h,hh,rfl⟩,rfl⟩|rfl)
  · exact Or.inl ⟨_,⟨h,old hh,rfl⟩,rfl⟩
  · exact Or.inr rfl

theorem normalized_member (Q : Palette G) {n : ℕ} (f : Signature (OI.K G) n)
    (retained : (⟨n,f⟩ : AnySignature (OI.K G))∈Q.family) :
    (⟨n,Pin.normalized G f⟩ : AnySignature AlgebraicComplex)∈family G Q := by
  change (⟨n,Pin.normalized G f⟩ : AnySignature AlgebraicComplex)∈
    GlobalCloseCompletionA0Family.finiteFamily G Q
  rw [←R.family_eq G Q]
  exact Or.inl ⟨⟨n,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f⟩,
    ⟨⟨n,f⟩,retained,rfl⟩,rfl⟩

structure Prepared : Type 1 where
  palette : Palette G
  old : P.family⊆palette.family
  row : GlobalCloseCompletionA0XSource.Row G palette
  nativeX : (⟨2,binarySignature (X : Binary (K:=OI.K G))⟩ : AnySignature (OI.K G))∈palette.family
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
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (r : GlobalCloseCompletionA0DenseEscape.SingularReceipt G P torsion q core literal)
variable (p : Bool)
variable (full : ∀x,Pin.normalized G q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p)

include torsion N core literal r full in
theorem prepared_exists : Nonempty (Prepared G P) := by
  let Q := U.palette G P torsion q core literal r
  have oldR := U.old G P torsion q core literal r
  have oldQ : P.family⊆Q.family := fun f hf=>oldR (U.old_base G P torsion q core literal hf)
  let pin := Pin.receipt G P torsion q core literal r
  have qa : Gadget.Realizes (R.family G Q) .disequality (Pin.normalized G q) := by
    apply Gadget.realizes_of_mem
    exact Or.inl ⟨⟨4,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q⟩,
      ⟨⟨4,q⟩,oldQ (literal ▸ core.retained),rfl⟩,rfl⟩
  obtain ⟨A,B,hA,hB,hcubic⟩ := GlobalCloseCompletionSingularSlice.exists_symmetric
    (R.family G Q) (GlobalCloseCompletionA0Family.identity G Q) (Pin.normalized G q) p full qa
    pin.coefficient pin.nonzero (pin.both_actual G P torsion q core literal r)
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
  let index := GlobalCloseCompletionA0Representatives.key G P torsion N false phase
  let binary := Holant.Projective.BoundedTorsion.binarySignature (actualRepresentative P.family torsion index)
  have binary_retained : (⟨2,binary⟩ : AnySignature (OI.K G))∈Q.family :=
    oldR (ClosureSourceRows.representative_retained G P torsion q core literal (by decide : 2≤2) index)
  have normalizedOld : R.family G Q⊆family G Q := by
    change R.family G Q⊆GlobalCloseCompletionA0Family.finiteFamily G Q
    rw [←R.family_eq G Q]
  let anchor : QuaternaryEqualityTerminal.AnchorStep (family G Q) :=
    { signature := cycle.output
      basis := cycle.basis
      edgeScale := 1
      vertexScale := cycle.coefficient
      edge_ne_zero := one_ne_zero
      vertex_ne_zero := cycle.coefficient_nonzero hA hB
      actual := cycle.actual.mono normalizedOld
      edge_exact := by simpa only [one_mul] using cycle.edge
      anchor_exact := cycle.normalized }
  let mu := GlobalCloseCompletionA0Representatives.multiplier G P torsion N false phase
  have mn : mu≠0 := (GlobalCloseCompletionA0Representatives.selection G P torsion N false phase).choose_spec.choose_spec.1
  have binaryNormal : Pin.normalized G binary=kernelSignature (scale mu (Holant.Marked.R t)) := by
    change GlobalCloseCompletionA0Workfield.basis.symm.action
      (kernelSignature ((actualRepresentative P.family torsion index).map (ClosureSourceRows.embedding G)))=_
    rw [transport_signature]
    exact congrArg kernelSignature (GlobalCloseCompletionA0Representatives.normal_form G P torsion N false phase)
  refine ⟨⟨Q,oldQ,U.row G P torsion q core literal r N,
    oldR (ClosureSourceRows.native_retained G P torsion q core literal (by decide : 2≤2)),
    anchor,rfl,binary,binary_retained,Ph.diagonal cycle.r cycle.u mu t,
    Ph.offDiagonal cycle.r cycle.u mu t,
    Ph.offDiagonal_nonzero _ _ _ _ cycle.r_nonzero cycle.u_nonzero mn hgap,
    Ph.nonsingular _ _ _ _ cycle.r_nonzero mn tn cycle.u_square,?_,
    pin.output,pin.retained,Pr.pinFirst cycle.r cycle.u pin.coefficient pin.bit,
    Pr.pinSecond cycle.r cycle.u pin.coefficient pin.bit,
    Pr.pinFirst_nonzero _ _ _ cycle.r_nonzero cycle.u_nonzero pin.nonzero pin.bit,
    Pr.pin_square _ _ _ pin.bit,?_⟩⟩
  · change cycle.basis.action (Pin.normalized G binary)=_
    rw [binaryNormal]
    exact Ph.normalization_phase _ _ _ _ cycle.r_nonzero cycle.u_nonzero
  · change cycle.basis.action (Pin.normalized G pin.output)=_
    rw [pin.exact]
    exact Pr.normalization_pin _ _ _ cycle.r_nonzero cycle.u_nonzero pin.bit

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0SingularPrepare
end
