import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0OpenCoordinate
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0CoordinateGate
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Family
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0RetainedRealizes
import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeCurrent

/-! Every gadget in the actual finite A0 native source has a genuine
projective gadget over original current P after the same Hadamard boundary
action. The original complete-group gate implements the inverse weighted
edge, and matching q4 retention supplies every restored old vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Backward
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionA0Workfield (basis)
end W
namespace C
export GlobalCloseCompletionA0CurrentSource (retained family)
end C
namespace Gate
export GlobalCloseCompletionA0CoordinateGate (gate coefficient coefficient_nonzero actual inverse_edge)
end Gate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

theorem forward_identity : W.basis.action (kernelSignature Signature.equality)=
    fun x => (2 : AlgebraicComplex)*kernelSignature Signature.equality x := by
  rw [InvertibleKernel.action,coordinateAction_kernelSignature]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [W.basis,GlobalCloseCompletionA0Workfield.basis,ClosureMarkedDihedralA0.basis,
      ClosureMarkedCyclic.basis,Holant.Marked.basisA,Holant.Marked.UA,
      kernelSignature,Kernel.mul_apply,Kernel.transpose,Signature.equality,h0,h1]

include stable in
theorem restored_member (f : AnySignature AlgebraicComplex)
    (member : f∈GlobalCloseCompletionA0Family.family G (C.retained G P torsion q core literal)) :
    Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality (W.basis.action f.2) := by
  rcases member with ⟨g,hg,rfl⟩ | equality
  · rw [InvertibleKernel.action_symm_action]
    obtain ⟨r,hr,rfl⟩ := hg
    have ha := RingHomRealization.realizes_map (ClosureSourceRows.embedding G)
      (GlobalCloseCompletionA0RetainedRealizes.member_actual G P torsion q core literal stable r hr)
    exact ⟨1,one_ne_zero,by simpa only [one_mul,RingHomRealization.mapAny] using ha⟩
  · change f=(⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) at equality
    subst f
    rw [forward_identity]
    have actualI : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
        (kernelSignature Signature.equality) := Gadget.realizes_of_mem _ .disequality _
          (StableDenseGaugeCurrent.ambient_identity G P)
    exact GlobalCloseCompletionA0OpenCoordinate.upTo_scale (ClosureSourceRows.ambientFamily G P)
      (kernelSignature Signature.equality)
      ⟨1,one_ne_zero,by simpa only [one_mul] using actualI⟩ 2 (by norm_num)

include N stable in
theorem backward {n : ℕ} (f : Signature AlgebraicComplex n)
    (actual : Gadget.Realizes (C.family G P torsion q core literal) .disequality f) :
    Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality (W.basis.action f) := by
  change Gadget.Realizes (GlobalCloseCompletionA0Family.finiteFamily G
    (C.retained G P torsion q core literal)) .disequality f at actual
  rw [←GlobalCloseCompletionA0Family.family_eq] at actual
  have edge : Kernel.pullback Signature.disequality W.basis.inverse=
      scale (Gate.coefficient G P torsion N)
        (GlobalCloseCompletionA0KernelRealizes.edge (Matrix.of (Gate.gate G P torsion N))) := by
    rw [GlobalCloseCompletionA0KernelRealizes.edge_kernel]
    exact Gate.inverse_edge G P torsion N
  exact GlobalCloseCompletionA0OpenCoordinate.coordinate (ClosureSourceRows.ambientFamily G P)
    (StableDenseGaugeCurrent.ambient_identity G P) (Matrix.of (Gate.gate G P torsion N))
    (Gate.actual G P torsion N) W.basis (Gate.coefficient G P torsion N)
    (Gate.coefficient_nonzero G P torsion N) edge
    (GlobalCloseCompletionA0Family.family G (C.retained G P torsion q core literal))
    (GlobalCloseCompletionA0Family.identity G (C.retained G P torsion q core literal))
    (restored_member G P torsion q core literal stable) f actual

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Backward
end
