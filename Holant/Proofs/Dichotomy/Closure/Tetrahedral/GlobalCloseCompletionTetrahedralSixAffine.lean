import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralAffineCards
import Holant.Platonic.StabilizerErasure.PhysicalTensorFrames
import Holant.Certificates.MatchingProductBridge.GroupInverses

/-! Affinity under the literal six independent T leg actions. The proof uses
finite coordinate substitution and summation of the existing affine class. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix.Affine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Certificates.MatchingProductBridge
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerShortening
open Holant.Platonic.StabilizerErasure
open scoped BigOperators

theorem sum_first {n : ℕ} {f : Signature ℂ (n+1)} (hf : ComplexAffine f) :
    ComplexAffine (fun x => f (Fin.cons false x)+f (Fin.cons true x)) := by
  obtain ⟨c,g,hg,he⟩ := hf
  refine ⟨c,_,hg.sum_first,?_⟩
  intro x
  simp only [he,Complex.ofReal_add]
  push_cast
  ring

def localAction (p : Fin 6) (M : Matrix Bool Bool ℂ) (f : Signature ℂ 6) : Signature ℂ 6 :=
  fun x => ∑ b : Bool, M (x p) b * f (Function.update x p b)

theorem local_affine (p : Fin 6) (M : Matrix Bool Bool ℂ)
    (hm : groupDirection .tetrahedral M) (f : Signature ℂ 6) (hf : ComplexAffine f) :
    ComplexAffine (localAction p M f) := by
  classical
  let u : Fin 6 → Fin 7 := fun j => if j=p then 0 else j.succ
  let v : Fin 2 → Fin 7 := ![p.succ,0]
  have hU := affine_complex_precompose hf (fun z j => z (u j)) (coordinates_isAffineMap u)
  have hV := affine_complex_precompose
    (GlobalCloseCompletionTetrahedralAffineCards.direction_affine M hm)
    (fun z j => z (v j)) (coordinates_isAffineMap v)
  have h := sum_first (affine_complex_mul hV hU)
  convert h using 1
  funext x
  have he (b : Bool) : (fun j => (Fin.cons b x : Fin 7 → Bool) (u j))=Function.update x p b := by
    funext j
    by_cases hj : j=p
    · subst j; simp [u]
    · simp [u,hj,Function.update_of_ne hj]
  simp only [localAction,Fintype.sum_bool,Holant.Projective.BoundedTorsion.binarySignature]
  simp [v,he,add_comm]

theorem local_single (p : Fin 6) (M : Matrix Bool Bool ℂ) (f : Signature ℂ 6) :
    Signature.coordinateAction (singleFrame p M) f=localAction p M f := by
  rw [coordinateAction_singleFrame]
  ext x
  simp [localAction,siteAction,Fin.insertNth_removeNth]

theorem coordinate_action (M : Fin 6 → Matrix Bool Bool ℂ)
    (hm : ∀j,groupDirection .tetrahedral (M j))
    (f : Signature ℂ 6) (hf : ComplexAffine f) :
    ComplexAffine (Signature.coordinateAction M f) := by
  have h := local_affine 5 (M 5) (hm 5) _
    (local_affine 4 (M 4) (hm 4) _
      (local_affine 3 (M 3) (hm 3) _
        (local_affine 2 (M 2) (hm 2) _
          (local_affine 1 (M 1) (hm 1) _ (local_affine 0 (M 0) (hm 0) f hf)))))
  have he : localAction 5 (M 5) (localAction 4 (M 4) (localAction 3 (M 3)
      (localAction 2 (M 2) (localAction 1 (M 1) (localAction 0 (M 0) f)))))=
      Signature.coordinateAction M f := by
    simp_rw [←local_single,Signature.coordinateAction_comp]
    congr 1
    funext j a b
    fin_cases j <;> cases a <;> cases b <;>
      simp [singleFrame,Kernel.mul,Signature.equality,Fintype.sum_bool]
  rwa [he] at h

theorem coordinate_action_iff (M : Fin 6 → Matrix Bool Bool ℂ)
    (hm : ∀j,groupDirection .tetrahedral (M j)) (f : Signature ℂ 6) :
    ComplexAffine (Signature.coordinateAction M f) ↔ ComplexAffine f := by
  constructor
  · intro hf
    let N : Fin 6 → Matrix Bool Bool ℂ := fun j => (M j)⁻¹
    have h := coordinate_action N
      (fun j => groupDirection_inverse .tetrahedral (hm j)) _ hf
    have he : Signature.coordinateAction N
        (Signature.coordinateAction M f)=f := by
      apply Signature.coordinateAction_cancel
      intro j
      change Kernel.mul (N j) (M j)=Signature.equality
      have hmul := Matrix.nonsing_inv_mul (M j)
        (isUnit_iff_ne_zero.mpr (groupDirection_det_ne_zero .tetrahedral (hm j)))
      ext a b
      have hentry := congrFun (congrFun hmul a) b
      simpa [N,Kernel.mul,Matrix.mul_apply,Matrix.one_apply,Signature.equality,Fintype.sum_bool] using hentry
    exact he ▸ h
  · exact coordinate_action M hm f

theorem reindex_iff (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6) :
    ComplexAffine (Tensor.reindex p f) ↔ ComplexAffine f := by
  constructor
  · intro hf
    have h := affine_complex_precompose hf (fun x j => x (p.symm j))
      (coordinates_isAffineMap p.symm)
    simpa only [Tensor.reindex,p.symm_apply_apply] using h
  · intro hf
    exact affine_complex_precompose hf (fun x j => x (p j)) (coordinates_isAffineMap p)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix.Affine
end
