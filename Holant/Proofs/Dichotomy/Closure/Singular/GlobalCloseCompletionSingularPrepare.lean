import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularSlice
import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularCycleReceipt
import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularPhaseBinary
import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularNAND

/-! Keep the same cycle basis while retaining an actual old native-M phase
binary beside the singular receipt's saved computational pin. The resulting
physical palette has the original-G programmes and no supplied hardness branch. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularPrepare
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.EightVertex.ProductAnchor
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace U
export StableDenseGaugeUnary (palette root root_nonzero unaryReceipt)
end U
namespace C
export GlobalCloseCompletionSingularCubicCycle (cubic)
export GlobalCloseCompletionSingularCycleReceipt (Receipt produce)
end C
namespace Pn
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePinAccess (scaledPin)
end Pn
namespace Ph
export GlobalCloseCompletionSingularPhaseBinary
  (diagonal offDiagonal normalization_phase nonsingular offDiagonal_nonzero choose_phase)
end Ph
namespace V
export GlobalCloseCompletionSingularNAND (traceless unary)
end V
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

private theorem mapped_pin {K : Type} [Field K] (phi : K→+*AlgebraicComplex) (b : Bool) (c : K) :
    RingHomRealization.mapSignature phi (Pn.scaledPin b c)=Pn.scaledPin b (phi c) := by
  funext x
  by_cases h : x 0=b <;> simp [RingHomRealization.mapSignature,Pn.scaledPin,h]

def pinFirst (r u c : AlgebraicComplex) (b : Bool) : AlgebraicComplex :=
  c*(if b then u/(2*r) else u/2)
def pinSecond (r u c : AlgebraicComplex) (b : Bool) : AlgebraicComplex :=
  c*(if b then -imaginaryUnit*u/(2*r) else imaginaryUnit*u/2)

theorem normalization_pin (r u c : AlgebraicComplex) (hr : r≠0) (hu : u≠0) (b : Bool) :
    (denseNormalization r u hr hu).action (Pn.scaledPin b c)=
      V.unary (pinFirst r u c b) (pinSecond r u c b) := by
  funext z
  change (∑y : Fin 1→Bool,(∏i,normalizationMatrix r u (z i) (y i))*Pn.scaledPin b c y)=_
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  cases b <;> cases h : z 0 <;>
    simp [Pn.scaledPin,V.unary,normalizationMatrix,Holant.EightVertex.ProductAnchor.matrix,
      pinFirst,pinSecond,h] <;> ring

theorem pinFirst_nonzero (r u c : AlgebraicComplex) (hr : r≠0) (hu : u≠0) (hc : c≠0) (b : Bool) :
    pinFirst r u c b≠0 := by
  unfold pinFirst
  apply mul_ne_zero hc
  cases b
  · exact div_ne_zero hu (by norm_num)
  · exact div_ne_zero hu (mul_ne_zero (by norm_num) hr)

theorem pin_square (r u c : AlgebraicComplex) (b : Bool) :
    (pinSecond r u c b)^2= -(pinFirst r u c b)^2 := by
  cases b <;> dsimp [pinFirst,pinSecond] <;> ring_nf <;> simp [imaginaryUnit_sq] <;> ring

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

structure Prepared : Type 1 where
  palette : Palette G
  old : ClosureSourceRows.ambientFamily G P⊆ClosureSourceRows.ambientFamily G palette
  anchor : QuaternaryEqualityTerminal.AnchorStep (ClosureSourceRows.ambientFamily G palette)
  edge_one : anchor.edgeScale=1
  binary : Signature (OI.K G) 2
  binary_retained : (⟨2,binary⟩ : AnySignature (OI.K G))∈palette.family
  x : AlgebraicComplex
  y : AlgebraicComplex
  y_nonzero : y≠0
  nonsingular : x^2+y^2≠0
  binary_exact : anchor.basis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) binary)=
    V.traceless x y
  unary : Signature (OI.K G) 1
  unary_retained : (⟨1,unary⟩ : AnySignature (OI.K G))∈palette.family
  u : AlgebraicComplex
  v : AlgebraicComplex
  u_nonzero : u≠0
  square : v^2= -u^2
  unary_exact : anchor.basis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) unary)=
    V.unary u v

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (r : StableDenseGaugeCurrent.SingularReceipt G P)
variable (q : Signature (OI.K G) 4) (p : Bool)
variable (full : ∀x,q x≠0 ↔ Holant.Marked.SupportAtlas.parity x=p)
variable (actual : Gadget.Realizes P.family .disequality q)

include torsion N r full actual in
theorem prepared_exists : Nonempty (Prepared G P) := by
  let Q := U.palette G P r
  have oldQ : P.family⊆Q.family := ProgrammeSaturation.retains_old G P (U.root G P r)
    (U.root_nonzero G P r) (by change 0<2; decide) r.actual
  obtain ⟨A,B,hA,hB,hcubic⟩ := GlobalCloseCompletionSingularSlice.ambient_symmetric G P r q p full actual
  rw [cubic_eq] at hcubic
  obtain ⟨cycle⟩ := C.produce _ A B hA hB hcubic
  have positive : 0<N.m := by have := N.range; omega
  let omega := ClosureMarkedDihedral.liftRoot positive N.omega N.primitive
  have different : omega≠1 := by
    intro eq
    have hv : (N.omega : ℂ)=1 := congrArg ClosureMarkedDihedral.inclusion eq
    have hu : N.omega=1 := Units.ext hv
    have hd : N.m∣1 := N.primitive.dvd_of_pow_eq_one 1 (by simp [hu])
    have := Nat.le_of_dvd (by decide : 0<1) hd
    have := N.range
    omega
  obtain ⟨t,ht,hgap⟩ := Ph.choose_phase cycle.r omega different
  have root : Roots N.m t := by
    rcases ht with rfl|rfl
    · exact Roots.one _
    · exact ClosureMarkedDihedral.liftRoot_root positive N.omega N.primitive
  have tn : t≠0 := by
    intro zero
    change t^N.m=1 at root
    rw [zero,zero_pow (by omega)] at root
    exact zero_ne_one root
  let phase : Holant.Marked.SupportAtlas.Phase N.m := ⟨t,root⟩
  let index := ClosureSourceRows.monomialIndex G P torsion N false phase
  let binary := Holant.Projective.BoundedTorsion.binarySignature (actualRepresentative P.family torsion index.key)
  have bn : binary≠0 := actualRepresentative_signature_nonzero P.family torsion index.key
  have ba : Gadget.Realizes Q.family .disequality binary :=
    (actualRepresentative_actual P.family torsion index.key).1.mono oldQ
  let W := ProgrammeSaturation.palette G Q ⟨2,binary⟩ bn (by change 0<2; decide) ba
  have oldW : Q.family⊆W.family := ProgrammeSaturation.retains_old G Q ⟨2,binary⟩ bn (by change 0<2; decide) ba
  have ambientW : ClosureSourceRows.ambientFamily G Q⊆ClosureSourceRows.ambientFamily G W := by
    rintro _ ⟨f,hf,rfl⟩
    exact ⟨f,oldW hf,rfl⟩
  let anchor : QuaternaryEqualityTerminal.AnchorStep (ClosureSourceRows.ambientFamily G W) :=
    { signature := cycle.output
      basis := cycle.basis
      edgeScale := 1
      vertexScale := cycle.coefficient
      edge_ne_zero := one_ne_zero
      vertex_ne_zero := cycle.coefficient_nonzero hA hB
      actual := cycle.actual.mono ambientW
      edge_exact := by simpa only [one_mul] using cycle.edge
      anchor_exact := cycle.normalized }
  let mu := ClosureSourceRows.embedding G index.coefficient
  have mn : mu≠0 := (map_ne_zero (ClosureSourceRows.embedding G)).mpr index.nonzero
  let pin := U.unaryReceipt G P r
  obtain ⟨bit,c,cn,pinEq⟩ := pin.pin
  change pin.output=Pn.scaledPin bit c at pinEq
  let cp := ClosureSourceRows.embedding G c
  have cpn : cp≠0 := (map_ne_zero (ClosureSourceRows.embedding G)).mpr cn
  refine ⟨⟨W,?_,anchor,rfl,binary,?_,Ph.diagonal cycle.r cycle.u mu t,
    Ph.offDiagonal cycle.r cycle.u mu t,
    Ph.offDiagonal_nonzero _ _ _ _ cycle.r_nonzero cycle.u_nonzero mn hgap,
    Ph.nonsingular _ _ _ _ cycle.r_nonzero mn tn cycle.u_square,?_,
    pin.output,oldW pin.retained,pinFirst cycle.r cycle.u cp bit,pinSecond cycle.r cycle.u cp bit,
    pinFirst_nonzero _ _ _ cycle.r_nonzero cycle.u_nonzero cpn bit,pin_square _ _ _ bit,?_⟩⟩
  · rintro _ ⟨f,hf,rfl⟩
    exact ⟨f,oldW (oldQ hf),rfl⟩
  · exact ProgrammeSaturation.retains_output G Q ⟨2,binary⟩ bn (by change 0<2; decide) ba
  · change cycle.basis.action (kernelSignature (ClosureSourceRows.representative G P torsion index.key))=_
    rw [index.normal]
    exact Ph.normalization_phase _ _ _ _ cycle.r_nonzero cycle.u_nonzero
  · change cycle.basis.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) pin.output)=_
    rw [pinEq,mapped_pin]
    exact normalization_pin _ _ _ cycle.r_nonzero cycle.u_nonzero bit

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularPrepare
end
