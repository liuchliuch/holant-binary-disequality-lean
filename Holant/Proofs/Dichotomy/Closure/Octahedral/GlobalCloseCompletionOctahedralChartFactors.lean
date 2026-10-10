import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralChartCards

/-! Analytic chart transport preserves the same original factor partition.
This is independent of arity and does not realize the coordinate matrices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralChart
open Holant Holant.Tractable Holant.Certificates.OctahedralSeparator
open Holant.Pauli.ExoticKlein.Fiber
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2

theorem inverse_nonzero (f : Form) {n : ℕ} (q : Signature ℂ n) (hq : q≠0) : inverse f q≠0 := by
  intro h
  have he := congrArg (action f) h
  rw [action_inverse] at he
  exact hq (by simpa only [action,Signature.coordinateAction_zero] using he)

theorem factor_inverse (f : Form) {n : ℕ} (q : Signature ℂ n) (factor : HasProperTensorFactor q) :
    HasProperTensorFactor (inverse f q) := by
  obtain ⟨a,b,ha,hb,p,u,v,hu,hv,he⟩ := factor
  refine ⟨a,b,ha,hb,p,inverse f u,inverse f v,
    inverse_nonzero f u hu,inverse_nonzero f v hv,?_⟩
  rw [he,inverse,ClosureFactorTreeAction.coordinateAction_tensor]
  rfl

theorem prime_no_chart_factor (f : Form) {n : ℕ} (q : Signature ℂ n)
    (prime : Prime (⟨n,q⟩ : AnySignature ℂ)) : ¬HasProperTensorFactor (action f q) := by
  intro factor
  have hf := factor_inverse f (action f q) factor
  rw [inverse_action] at hf
  obtain ⟨a,b,ha,hb,p,u,v,_,_,he⟩ := hf
  apply prime.2
  exact ⟨⟨a,u⟩,⟨b,v⟩,⟨{
    left_pos:=ha
    right_pos:=hb
    ports:=p
    scale:=1
    equation:=by
      funext x
      change q x=(1 : ℂ)*(u (fun i=>x (p (.inl i)))*v (fun i=>x (p (.inr i))))
      simpa only [Tensor.reindex,Tensor.tensor,one_mul] using congrFun he x }⟩⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralChart
end
