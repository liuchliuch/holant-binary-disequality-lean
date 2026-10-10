import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralFrames
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralAffineCards
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicMatchingCone
import Holant.Holographic

/-! All-arity matching transport in the four actual O coefficient charts.
The Gram factor H Hᵀ is an explicit standard-O direction, and is retained
on both the physical factor and contraction-kernel identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralChart
open Holant Holant.Tractable Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerShortening
open GlobalCloseCompletionOctahedralGeometry
open RankFour.ExactAutomorphisms RankFour.TwoSidedCompleteness
open scoped BigOperators

def H (f : Form) : Matrix Bool Bool ℂ := rowMatrix f

def action (f : Form) {n : ℕ} (q : Signature ℂ n) :=
  Signature.coordinateAction (fun _=>H f) q

def inverse (f : Form) {n : ℕ} (q : Signature ℂ n) :=
  Signature.coordinateAction (fun _=>@Inv.inv (Matrix Bool Bool ℂ) Matrix.inv (H f)) q

theorem inverse_action (f : Form) {n : ℕ} (q : Signature ℂ n) : inverse f (action f q)=q := by
  apply Signature.coordinateAction_cancel
  intro j
  change (H f)⁻¹*H f=1
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (rowMatrix_det f))

theorem action_inverse (f : Form) {n : ℕ} (q : Signature ℂ n) : action f (inverse f q)=q := by
  apply Signature.coordinateAction_cancel
  intro j
  change H f*(H f)⁻¹=1
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (rowMatrix_det f))

theorem gram_direction (f : Form) : groupDirection .octahedral (frameS f) := by
  obtain ⟨c,hc,k,he⟩ := frameS_direction f
  exact (source_group_iff_standard _).mpr ⟨c,hc,k,by simpa only [theta_zero] using he⟩

theorem factor_direction (f : Form) (U : Matrix Bool Bool ℂ) (member : Direction f U) :
    groupDirection .octahedral (H f*U*(H f).transpose) := by
  have hm := Holant.Certificates.RainbowOrbit.groupDirection_mul .octahedral ((direction_iff_source_pull f U).mp member)
    (gram_direction f)
  have he : complexPull f U*frameS f=H f*U*(H f).transpose := by
    rw [frameS_product]
    change (H f*(U*(H f)⁻¹))*(H f*(H f).transpose)=H f*U*(H f).transpose
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc ((H f)⁻¹),
      Matrix.nonsing_inv_mul (H f) (isUnit_iff_ne_zero.mpr (rowMatrix_det f)),Matrix.one_mul]
  rwa [he] at hm

theorem pair_direction (f : Form) (K : Matrix Bool Bool ℂ) (member : groupDirection .octahedral K) :
    Direction f ((H f).transpose*K*H f) := by
  apply (direction_iff_source_pull f _).mpr
  have he : complexPull f ((H f).transpose*K*H f)=frameS f*K := by
    rw [frameS_product]
    change H f*(((H f).transpose*K*H f)*(H f)⁻¹)=(H f*(H f).transpose)*K
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv (H f) (isUnit_iff_ne_zero.mpr (rowMatrix_det f)),Matrix.mul_one]
  rw [he]
  exact Holant.Certificates.RainbowOrbit.groupDirection_mul .octahedral (gram_direction f) member

theorem coordinateAction_productValue {n r : ℕ} (p : (Fin r × Bool) ≃ Fin n)
    (A : Kernel ℂ) (B : Fin r → Kernel ℂ) (κ : ℂ) :
    Signature.coordinateAction (fun _ => A) (productValue p B κ) =
      productValue p (fun e a b => ∑ u : Bool, ∑ v : Bool, A a u * A b v * B e u v) κ := by
  funext x
  simp only [Signature.coordinateAction, productValue]
  rw [← (Equiv.arrowCongr p (Equiv.refl Bool)).sum_comp
    (fun y : Fin n → Bool => (∏ j : Fin n, A (x j) (y j)) *
      (κ * ∏ e : Fin r, B e (y (p (e,false))) (y (p (e,true)))))]
  simp only [Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply, Equiv.symm_apply_apply]
  change (∑ y : (Fin r × Bool) → Bool,
    (∏ j : Fin n, A (x j) (y (p.symm j))) *
      (κ * ∏ e, B e (y (e,false)) (y (e,true)))) = _
  have hp (y : (Fin r × Bool) → Bool) :
      (∏ j : Fin n, A (x j) (y (p.symm j))) =
        ∏ e : Fin r, A (x (p (e,false))) (y (e,false)) *
          A (x (p (e,true))) (y (e,true)) := by
    rw [←p.prod_comp (fun j => A (x j) (y (p.symm j)))]
    simp only [Equiv.symm_apply_apply, Fintype.prod_prod_type, Fintype.prod_bool]
    apply Finset.prod_congr rfl
    intro e _
    exact mul_comm _ _
  simp_rw [hp]
  calc
    _ = κ * ∑ y : (Fin r × Bool) → Bool, ∏ e : Fin r,
        A (x (p (e,false))) (y (e,false)) *
          A (x (p (e,true))) (y (e,true)) * B e (y (e,false)) (y (e,true)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [Network.sum_halfEdge_products r
      (fun e a b => A (x (p (e,false))) a * A (x (p (e,true))) b * B e a b)]


theorem presentation_action {n : ℕ} (f : Form) (M : Presentation ℂ (Fin n)) :
    action f M.tensor=
      (⟨M.edges,M.ports,fun e=>H f*M.matrix e*(H f).transpose,M.scalar⟩ : Presentation ℂ (Fin n)).tensor := by
  rw [action,Presentation.tensor,coordinateAction_productValue]
  congr 1
  funext e a b
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem presentation_affine {n : ℕ} (f : Form) (M : Presentation ℂ (Fin n))
    (member : ∀e,Direction f (M.matrix e)) : ComplexAffine (action f M.tensor) := by
  rw [presentation_action]
  exact GlobalCloseCompletionOctahedralAffineCards.presentation_affine _
    (fun e=>factor_direction f (M.matrix e) (member e))

theorem presentation_cone (f : Form) (M : Presentation ℂ (Fin 4))
    (member : ∀e,Direction f (M.matrix e)) : matchingCone .octahedral (action f M.tensor) := by
  rw [presentation_action]
  exact GlobalCloseCompletionPlatonicMatchingCone.presentation .octahedral _
    (fun e=>factor_direction f (M.matrix e) (member e))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralChart
end
