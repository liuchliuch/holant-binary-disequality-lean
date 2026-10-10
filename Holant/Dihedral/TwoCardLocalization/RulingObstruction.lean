import Holant.Dihedral.TwoCardLocalization.MonomialUniqueness

/-! The intrinsic terminal disagreement excludes a common matching with even
one fixed ordered factor line. All comparisons are derived from full products. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
open Holant.Dihedral.EndpointParallelogram Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false

def RulingPair (m : ℕ) (q₀ q₁ : Signature Scalar 4) : Prop :=
  ∃ r : ℕ, ∃ p : (Fin r × Bool) ≃ Fin 4, ∃ A₀ A₁ : Fin r → Mat, ∃ κ₀ κ₁ : Scalar,
    (∀ e,A₀ e ∈ groupM m) ∧ (∀ e,A₁ e ∈ groupM m) ∧ κ₀ ≠ 0 ∧ κ₁ ≠ 0 ∧
    q₀=MatchingContractionClosure.productValue p A₀ κ₀ ∧
    q₁=MatchingContractionClosure.productValue p A₁ κ₁ ∧ ∃ e,ProjectivelyEqual (A₁ e) (A₀ e)

theorem rulingPair_of_finite {m : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (p : (E × Bool) ≃ Fin 4) (A₀ A₁ : E → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,A₀ e ∈ groupM m) (hA₁ : ∀ e,A₁ e ∈ groupM m)
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e : E) (he : ProjectivelyEqual (A₁ e) (A₀ e)) :
    RulingPair m (MatchingContractionClosure.productValue p A₀ κ₀)
      (MatchingContractionClosure.productValue p A₁ κ₁) := by
  let s := Fintype.equivFin E
  let p' := (Equiv.prodCongr s.symm (Equiv.refl Bool)).trans p
  refine ⟨Fintype.card E,p',fun d => A₀ (s.symm d),fun d => A₁ (s.symm d),κ₀,κ₁,
    fun d => hA₀ _,fun d => hA₁ _,hκ₀,hκ₁,?_,?_,s e,?_⟩
  · exact (MatchingContractionClosure.Presentation.ofFinite_tensor p A₀ κ₀).symm
  · exact (MatchingContractionClosure.Presentation.ofFinite_tensor p A₁ κ₁).symm
  · simpa only [Equiv.symm_apply_apply] using he

theorem rulingPair_reindexed {m : ℕ} {E P : Type*} [Fintype E] [DecidableEq E] [DecidableEq P]
    (p : (E × Bool) ≃ P) (order : P ≃ Fin 4) (A₀ A₁ : E → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,A₀ e ∈ groupM m) (hA₁ : ∀ e,A₁ e ∈ groupM m)
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e : E) (he : ProjectivelyEqual (A₁ e) (A₀ e)) :
    RulingPair m (Tensor.reindex order (MatchingContractionClosure.productValue p A₀ κ₀))
      (Tensor.reindex order (MatchingContractionClosure.productValue p A₁ κ₁)) :=
  rulingPair_of_finite (p.trans order) A₀ A₁ κ₀ κ₁ hA₀ hA₁ hκ₀ hκ₁ e he

theorem projective_transpose {A B : Mat} (h : ProjectivelyEqual A B) :
    ProjectivelyEqual (Kernel.transpose A) (Kernel.transpose B) := by
  obtain ⟨c,hc,rfl⟩ := h
  exact ⟨c,hc,rfl⟩

/-- A pair with distinct residual matchings, or with both ordered factor lines
different, cannot be two nonzero members of one one-factor Segre ruling. -/
theorem disagreement_not_ruling {m : ℕ} (hm : 0<m) {q₀ q₁ : Signature Scalar 4}
    (hd : Disagreement m 4 q₀ q₁) : ¬ RulingPair m q₀ q₁ := by
  rintro ⟨r,p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,hq₀,hq₁,j,hj⟩
  have hr : r=2 := by
    have hh := Fintype.card_congr p
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
    omega
  subst r
  have hmono₀ e := groupM_isMonomial hm (hA₀ e)
  have hmono₁ e := groupM_isMonomial hm (hA₁ e)
  rcases hd with hd|hd
  · obtain ⟨M₀,M₁,hM₀,hM₁,hc₀,hc₁,hQ₀,hQ₁,hne⟩ := hd
    have hN₀ e := groupM_isMonomial hm ((safe_groupM_iff hm _).mp (hM₀ e))
    have hN₁ e := groupM_isMonomial hm ((safe_groupM_iff hm _).mp (hM₁ e))
    have he₀ := product_matching_unique p M₀.ports A₀ M₀.matrix κ₀ M₀.scalar hmono₀ hN₀ hκ₀ hc₀ (hq₀.symm.trans hQ₀)
    have he₁ := product_matching_unique p M₁.ports A₁ M₁.matrix κ₁ M₁.scalar hmono₁ hN₁ hκ₁ hc₁ (hq₁.symm.trans hQ₁)
    apply hne
    apply Equiv.ext
    intro u
    exact congrArg (fun M : Pairing (Fin 4) => M.mate u) (he₀.symm.trans he₁)
  · obtain ⟨q,B₀,B₁,c₀,c₁,hB₀,hB₁,hc₀,hc₁,hQ₀,hQ₁,htags⟩ := two_tags_four_exact hd
    have hN₀ e := groupM_isMonomial hm (hB₀ e)
    have hN₁ e := groupM_isMonomial hm (hB₁ e)
    have he₀ := product_matching_unique p q A₀ B₀ κ₀ c₀ hmono₀ hN₀ hκ₀ hc₀ (hq₀.symm.trans hQ₀)
    let L := MatchingAlignment.ofMate p q (fun u => congrArg (fun M : Pairing (Fin 4) => M.mate u) he₀)
    have hl₀ : MatchingContractionClosure.productValue p (L.factors B₀) c₀ =
        MatchingContractionClosure.productValue q B₀ c₀ := L.product_eq B₀ c₀
    have hl₁ : MatchingContractionClosure.productValue p (L.factors B₁) c₁ =
        MatchingContractionClosure.productValue q B₁ c₁ := L.product_eq B₁ c₁
    have hL₀ e : IsMonomial (L.factors B₀ e) := by
      unfold MatchingAlignment.factors
      split
      · exact (hN₀ _).transpose
      · exact hN₀ _
    have hL₁ e : IsMonomial (L.factors B₁ e) := by
      unfold MatchingAlignment.factors
      split
      · exact (hN₁ _).transpose
      · exact hN₁ _
    have hf₀ := product_factor_line_unique p A₀ (L.factors B₀) κ₀ c₀ hL₀ hκ₀ hc₀
      ((hq₀.symm.trans hQ₀).trans hl₀.symm) j
    have hf₁ := product_factor_line_unique p A₁ (L.factors B₁) κ₁ c₁ hL₁ hκ₁ hc₁
      ((hq₁.symm.trans hQ₁).trans hl₁.symm) j
    have hp : ProjectivelyEqual (L.factors B₁ j) (L.factors B₀ j) := hf₁.trans (hj.trans hf₀.symm)
    apply htags (L.edge j)
    cases hflip : L.flip j
    · simpa only [MatchingAlignment.factors,hflip,ite_false,Bool.false_eq_true] using hp
    · have ht := projective_transpose hp
      simpa only [MatchingAlignment.factors,hflip,ite_true,Kernel.transpose_transpose] using ht

end Holant.Dihedral.TwoCardLocalization
