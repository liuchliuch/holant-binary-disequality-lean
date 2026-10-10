import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralEndpointCurrent
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralDenseData
import Holant.Proofs.Dichotomy.Main.PaperControlled.OctahedralDenseResolved

/-! All dense marked O endpoints give the same whole-current source contract.
The td phase correction is a physical original binary; only afterwards is
the actual algebraic canonical Eq4 coordinate change applied analytically. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.OctahedralDenseEndpoint
open Holant Holant.Tractable Holant.Algebraic Holant.Projective.BoundedTorsion
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry
open Holant.EightVertex.ProductAnchor
open scoped BigOperators
namespace E
export GlobalCloseCompletionOctahedralEndpointCurrent (Output)
end E
namespace D
export GlobalCloseCompletionOctahedralDressing (Tensor ψ mappedSignature transport_slots targetSlots)
end D
namespace N
export GlobalCloseCompletionOctahedralDenseData
  (weight weight_nonzero weight_eighth codes slots scalar scalar_nonzero action_exact phase_member)
end N
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)
variable (output : E.Output G P tau) (dense : output.form≠0)

private theorem inclusion_apply (z : AlgebraicComplex) :
    (algebraicClosure ℚ ℂ).val.toRingHom z = (z : ℂ) := rfl

include output dense in
theorem canonical : Nonempty
    (GlobalCloseCompletionBDenseCanonical.Canonical (ClosureSourceRows.ambientFamily G P)) := by
  have slots : (fun i=>complexMatrix (N.slots output.form i))=
      fun i=>(1 : ℂ) • D.targetSlots output.form (N.codes output.form) (fun _=>false) i := by
    funext i
    simp [D.targetSlots,Preserver.kernel,GlobalCloseCompletionOctahedralDenseData.slots]
  obtain ⟨Q,alpha,ha,hQ⟩ := D.transport_slots G P tau output.form output.group_eq output.tensor
    (N.codes output.form) (fun _=>false) _ (fun _=>1) (fun _=>one_ne_zero) slots
  let c : AlgebraicComplex := (ClosureSourceRows.embedding G) (Q.table (fun _=>false))
  let d : ℂ := alpha*(output.scalar*embed (N.scalar output.form))
  have hd : d≠0 := mul_ne_zero ha (mul_ne_zero output.nonzero
    (embed_ne_zero (N.scalar_nonzero output.form)))
  have he : RingHomRealization.mapSignature (D.ψ G) Q.table=
      d • RingHomRealization.mapSignature (algebraicClosure ℚ ℂ).val.toRingHom
        (denseTensor 1 (N.weight output.form) (fun _=>false)) := by
    rw [hQ,output.coefficients,GlobalCloseCompletionOctahedralNormalized.action_smul,
      N.action_exact output.form dense,smul_smul,smul_smul,mul_assoc]
  have hc : (c : ℂ)=d := by
    change D.ψ G (Q.table (fun _=>false))=d
    have h := congrFun he (fun _=>false)
    simpa [RingHomRealization.mapSignature,denseTensor,Holant.weight,bitSign] using h
  have hc0 : c≠0 := by
    intro hz
    apply hd
    simpa only [hz,ZeroMemClass.coe_zero] using hc.symm
  have exactValue : D.mappedSignature G Q.table=
      denseTensor c (N.weight output.form) (fun _=>false) := by
    funext x
    apply (algebraicClosure ℚ ℂ).val.toRingHom.injective
    change D.ψ G (Q.table x) =
      (algebraicClosure ℚ ℂ).val.toRingHom (denseTensor c (N.weight output.form) (fun _=>false) x)
    have h := congrFun he x
    by_cases hx : Holant.weight x%2=0 <;>
      simpa [RingHomRealization.mapSignature,denseTensor,bitSign,hx,inclusion_apply,hc,mul_assoc] using h
  have actual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
      (denseTensor c (N.weight output.form) (fun _=>false)) := by
    rw [←exactValue]
    exact RingHomRealization.realizes_map (ClosureSourceRows.embedding G) Q.actual
  exact GlobalCloseCompletionOctahedralDenseCanonical.of_dense G P tau output.form output.group_eq
    c (N.weight output.form) hc0 (N.weight_nonzero output.form) (N.weight_eighth output.form)
    actual (N.phase_member output.form)

include output dense in
theorem classified : GlobalCloseCompletionEq4Classification.CurrentTract G P ∨
    PaperControlledHardness.Original G := by
  obtain ⟨C⟩ := canonical G P tau output dense
  exact PaperControlled.OctahedralDenseResolved.classified G P C


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.OctahedralDenseEndpoint
end
