import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralExternalCone
import Holant.Platonic.RankDeficientLocalization.Normalization.CardPresentations

/-! The actual external-T four-port matching cone has no rainbow image
under any linear kernel map. The existing Q2 obstruction is applied only
after the real factors, matchings and nonzero line coefficients are recovered. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalNoRainbow
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit
open Holant.Platonic.RankDeficientLocalization
open Holant.Platonic.RankDeficientLocalization.Normalization
open GlobalCloseCompletionOctahedralExternalCone

private def PointIn (r : Fin 3) (p : RainbowOrbit.Point) : Prop :=
  ∃F,∃hF : F≠0,External.InMatching r F ∧ p=Projectivization.mk ℂ F hF

private theorem ordered_no_rainbow {p q t : RainbowOrbit.Point}
    (hp : PointIn 0 p) (hq : PointIn 1 q) (ht : PointIn 2 t)
    (hc : Projectivization.IsCollinear {p,q,t}) : False := by
  apply External.no_rainbow ![p,q,t]
  constructor
  · intro r
    fin_cases r
    · exact hp
    · exact hq
    · exact ht
  · exact hc

private theorem unordered_no_rainbow (r₀ r₁ r₂ : Fin 3) {p q t : RainbowOrbit.Point}
    (hp : PointIn r₀ p) (hq : PointIn r₁ q) (ht : PointIn r₂ t)
    (h01 : r₀≠r₁) (h20 : r₂≠r₀) (h21 : r₂≠r₁)
    (hc : Projectivization.IsCollinear {p,q,t}) : False := by
  fin_cases r₀ <;> fin_cases r₁ <;> fin_cases r₂ <;> simp_all only [ne_eq,not_true_eq_false]
  all_goals first
    | exact ordered_no_rainbow hp hq ht hc
    | exact ordered_no_rainbow hp ht hq (by convert hc using 1 <;> ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto)
    | exact ordered_no_rainbow hq hp ht (by convert hc using 1 <;> ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto)
    | exact ordered_no_rainbow hq ht hp (by convert hc using 1 <;> ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto)
    | exact ordered_no_rainbow ht hp hq (by convert hc using 1 <;> ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto)
    | exact ordered_no_rainbow ht hq hp (by convert hc using 1 <;> ext x <;> simp only [Set.mem_insert_iff,Set.mem_singleton_iff] <;> tauto)

theorem no_rainbow {n : ℕ} (Φ : Holant.Certificates.PlatonicIncidence.Mat→ₗ[ℂ] FourTensor) (U : Fin n→Holant.Certificates.PlatonicIncidence.Mat)
    (cards : ∀i,Cone (Φ (U i))) (R : RainbowDomainLine Φ U) : False := by
  obtain ⟨r₀,A₀,B₀,hA₀,hB₀,he₀⟩ := (cards R.first).resolve_left R.card₀.nonzero
  obtain ⟨r₁,A₁,B₁,hA₁,hB₁,he₁⟩ := (cards R.second).resolve_left R.card₁.nonzero
  obtain ⟨r₂,A₂,B₂,hA₂,hB₂,he₂⟩ := (cards R.third).resolve_left R.card₂.nonzero
  have hm₀ := card_matching_of_tensor R.card₀ hA₀.det_ne_zero hB₀.det_ne_zero he₀
  have hm₁ := card_matching_of_tensor R.card₁ hA₁.det_ne_zero hB₁.det_ne_zero he₁
  have hm₂ := card_matching_of_tensor R.card₂ hA₂.det_ne_zero hB₂.det_ne_zero he₂
  have h01 : r₀≠r₁ := by intro h;exact R.different₀₁ (hm₀.trans (h ▸ hm₁.symm))
  have h20 : r₂≠r₀ := by intro h;exact R.different₂₀ (hm₂.trans (h ▸ hm₀.symm))
  have h21 : r₂≠r₁ := by intro h;exact R.different₂₁ (hm₂.trans (h ▸ hm₁.symm))
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp R.third_mem
  have hline : Φ (U R.third)=a • Φ (U R.first)+b • Φ (U R.second) := by
    rw [←map_smul,←map_smul,←map_add,hab]
  have ha : a≠0 := by
    intro hz
    have hb : b≠0 := by intro hb;exact R.card₂.nonzero (by simpa [hz,hb] using hline)
    exact R.card₂.not_proportional R.card₁ R.different₂₁
      ⟨b,hb,by simpa [hz] using hline⟩
  have hb : b≠0 := by
    intro hz
    exact R.card₂.not_proportional R.card₀ R.different₂₀
      ⟨a,ha,by simpa [hz] using hline⟩
  have hc : Projectivization.IsCollinear
      {Projectivization.mk ℂ (Φ (U R.first)) R.card₀.nonzero,
       Projectivization.mk ℂ (Φ (U R.second)) R.card₁.nonzero,
       Projectivization.mk ℂ (Φ (U R.third)) R.card₂.nonzero} :=
    (collinear_triple_iff _ _ _ R.card₀.nonzero R.card₁.nonzero R.card₂.nonzero
      (R.card₀.not_proportional R.card₁ R.different₀₁)
      (R.card₂.not_proportional R.card₀ R.different₂₀)
      (R.card₂.not_proportional R.card₁ R.different₂₁)).mpr ⟨a,b,ha,hb,hline⟩
  exact unordered_no_rainbow r₀ r₁ r₂
    ⟨_,R.card₀.nonzero,⟨A₀,B₀,hA₀,hB₀,he₀⟩,rfl⟩
    ⟨_,R.card₁.nonzero,⟨A₁,B₁,hA₁,hB₁,he₁⟩,rfl⟩
    ⟨_,R.card₂.nonzero,⟨A₂,B₂,hA₂,hB₂,he₂⟩,rfl⟩ h01 h20 h21 hc

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalNoRainbow
end
