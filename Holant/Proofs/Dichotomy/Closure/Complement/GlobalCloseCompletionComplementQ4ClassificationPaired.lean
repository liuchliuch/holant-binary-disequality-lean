import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationScale
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4SupportBasis
import Holant.Proofs.Dichotomy.Retained.StableDenseParityAlgebra
import Holant.Proofs.Dichotomy.Retained.StableDenseResidualGaugeCore

/-! The paired-square exceptional branch retains a concrete resource.
Real signs give a dense equal-products support projector. The other fourth
roots give an actual two-block series square, with its exact scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationPaired
open Holant
namespace S
export GlobalCloseCompletionComplementQ4Series (row spectrum ofSpectrum connected)
end S
namespace P
export GlobalCloseCompletionComplementQ4SupportBasis (support)
end P
namespace Sc
export GlobalCloseCompletionComplementQ4ClassificationScale (row_smul)
end Sc
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem fourth_split (r : K) (fourth : r^4=1) : r^2=1 ∨ r^2= -1 := by
  have h : (r^2-1)*(r^2+1)=0 := by linear_combination fourth
  rcases mul_eq_zero.mp h with h|h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem signed (r t u : K) (squares : u^2=r^2*t^2) :
    ∃s : K,s^2=1 ∧ u=s*r*t := by
  have h : u^2=(r*t)^2 := by simpa only [mul_pow] using squares
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h|h
  · exact ⟨1,by norm_num,by simpa using h⟩
  · exact ⟨-1,by norm_num,by simpa using h⟩

theorem support_scale (a : K) (ha : a≠0) (v : Fin 4→K) :
    P.support (fun i=>a*v i)=P.support v := by
  classical
  funext i
  simp [P.support,ha]

theorem real_support (r s t : K) (hr : r^2=1) (hs : s^2=1) (ht : t≠0) :
    S.ofSpectrum (P.support (S.spectrum 1 r t (s*r*t)))=
      S.row (r/2) (1/2) ((s*r)/2) (1/2) := by
  have hp : t+t≠0 := by simpa only [two_mul] using mul_ne_zero (by norm_num : (2:K)≠0) ht
  have hm : -t+-t≠0 := by simpa only [neg_add_rev] using neg_ne_zero.mpr hp
  rcases sq_eq_one_iff.mp hr with rfl|rfl <;> rcases sq_eq_one_iff.mp hs with rfl|rfl
  all_goals
    unfold S.ofSpectrum
    congr 1 <;> norm_num [P.support,S.spectrum,ht,hp,hm,sub_eq_add_neg]

theorem dense (r s : K) (hr : r^2=1) (hs : s^2=1) :
    StableDenseParityAlgebra.Dense (S.row (r/2) (1/2) ((s*r)/2) (1/2)) := by
  have rn : r≠0 := by intro h;simpa [h] using hr
  have sn : s≠0 := by intro h;simpa [h] using hs
  change r/2≠0 ∧ (1:K)/2≠0 ∧ s*r/2≠0 ∧ (1:K)/2≠0 ∧ (1:K)/2≠0 ∧ s*r/2≠0 ∧ (1:K)/2≠0 ∧ r/2≠0
  have two : (2:K)≠0 := by norm_num
  exact ⟨div_ne_zero rn two,div_ne_zero one_ne_zero two,div_ne_zero (mul_ne_zero sn rn) two,
    div_ne_zero one_ne_zero two,div_ne_zero one_ne_zero two,div_ne_zero (mul_ne_zero sn rn) two,
    div_ne_zero one_ne_zero two,div_ne_zero rn two⟩

theorem products (r s : K) (hr : r^2=1) (hs : s^2=1) :
    StableDenseResidualGaugeCore.Products (S.row (r/2) (1/2) ((s*r)/2) (1/2)) := by
  change (r/2)*(r/2)=(1/2)*(1/2) ∧ (r/2)*(r/2)=(s*r/2)*(s*r/2) ∧ (r/2)*(r/2)=(1/2)*(1/2)
  constructor
  · linear_combination hr/4
  constructor
  · linear_combination -(r^2/4)*hs
  · linear_combination hr/4

theorem imaginary_square (L : Network K 4) (a r s t : K)
    (form : L.denote=a • S.row 1 r t (s*r*t)) (hr : r^2= -1) (hs : s^2=1) :
    (Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork.connect L L false).denote=
      S.row (2*a^2*r) 0 (2*a^2*s*r*t^2) 0 := by
  rw [Sc.row_smul] at form
  rw [S.connected L L _ _ _ _ _ _ _ _ form form]
  congr 1
  · ring
  · linear_combination a^2*hr
  · ring
  · linear_combination (a^2*s^2*t^2)*hr-(a^2*t^2)*hs


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationPaired
end
