import Holant.Dihedral.TwoCardLocalization.Group

/-! Two literal protected original factor lines on one common matching. The
indices name actual matrix entries in the complete coefficient products. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
set_option backward.isDefEq.respectTransparency false

def TwoTags (m n : ℕ) (q₀ q₁ : Signature Scalar n) : Prop :=
  ∃ r : ℕ, ∃ p : (Fin r × Bool) ≃ Fin n, ∃ A₀ A₁ : Fin r → Mat, ∃ κ₀ κ₁ : Scalar,
    (∀ e,A₀ e ∈ groupM m) ∧ (∀ e,A₁ e ∈ groupM m) ∧ κ₀ ≠ 0 ∧ κ₁ ≠ 0 ∧
    q₀=MatchingContractionClosure.productValue p A₀ κ₀ ∧
    q₁=MatchingContractionClosure.productValue p A₁ κ₁ ∧
    ∃ e f : Fin r,e ≠ f ∧ ¬ ProjectivelyEqual (A₁ e) (A₀ e) ∧ ¬ ProjectivelyEqual (A₁ f) (A₀ f)

/-- Finite edge re-enumeration keeps the exact two protected matrix entries. -/
theorem two_tags_of_finite {m n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (p : (E × Bool) ≃ Fin n) (A₀ A₁ : E → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,A₀ e ∈ groupM m) (hA₁ : ∀ e,A₁ e ∈ groupM m)
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e f : E) (hef : e ≠ f)
    (he : ¬ ProjectivelyEqual (A₁ e) (A₀ e)) (hf : ¬ ProjectivelyEqual (A₁ f) (A₀ f)) :
    TwoTags m n (MatchingContractionClosure.productValue p A₀ κ₀)
      (MatchingContractionClosure.productValue p A₁ κ₁) := by
  let s := Fintype.equivFin E
  let p' := (Equiv.prodCongr s.symm (Equiv.refl Bool)).trans p
  refine ⟨Fintype.card E,p',fun d => A₀ (s.symm d),fun d => A₁ (s.symm d),κ₀,κ₁,
    fun d => hA₀ _,fun d => hA₁ _,hκ₀,hκ₁,?_,?_,s e,s f,fun h => hef (s.injective h),?_,?_⟩
  · exact (MatchingContractionClosure.Presentation.ofFinite_tensor p A₀ κ₀).symm
  · exact (MatchingContractionClosure.Presentation.ofFinite_tensor p A₁ κ₁).symm
  · simpa only [Equiv.symm_apply_apply] using he
  · simpa only [Equiv.symm_apply_apply] using hf

/-- The concrete residual-port surgery can be put in any proved external order
without changing protected factor lines or the complete coefficients. -/
theorem two_tags_reindexed {m n : ℕ} {E P : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq P] (p : (E × Bool) ≃ P) (order : P ≃ Fin n)
    (A₀ A₁ : E → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,A₀ e ∈ groupM m) (hA₁ : ∀ e,A₁ e ∈ groupM m)
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e f : E) (hef : e ≠ f)
    (he : ¬ ProjectivelyEqual (A₁ e) (A₀ e)) (hf : ¬ ProjectivelyEqual (A₁ f) (A₀ f)) :
    TwoTags m n (Tensor.reindex order (MatchingContractionClosure.productValue p A₀ κ₀))
      (Tensor.reindex order (MatchingContractionClosure.productValue p A₁ κ₁)) :=
  two_tags_of_finite (p.trans order) A₀ A₁ κ₀ κ₁ hA₀ hA₁ hκ₀ hκ₁ e f hef he hf

theorem TwoTags.scale {m n : ℕ} {q₀ q₁ : Signature Scalar n} (h : TwoTags m n q₀ q₁)
    (c : Scalar) (hc : c ≠ 0) : TwoTags m n (c • q₀) (c • q₁) := by
  obtain ⟨r,p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,rfl,rfl,he⟩ := h
  refine ⟨r,p,A₀,A₁,c*κ₀,c*κ₁,hA₀,hA₁,mul_ne_zero hc hκ₀,mul_ne_zero hc hκ₁,?_,?_,he⟩
  all_goals funext x; simp [MatchingContractionClosure.productValue,Pi.smul_apply,smul_eq_mul,mul_assoc]

theorem TwoTags.nonzero {m n : ℕ} (hm : 0<m) {q₀ q₁ : Signature Scalar n}
    (h : TwoTags m n q₀ q₁) : q₀ ≠ 0 ∧ q₁ ≠ 0 := by
  obtain ⟨r,p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,rfl,rfl,_⟩ := h
  have hn₀ e := MatchingContractionClosure.SafeBinary.nonsingular (groupM_matrix_group hm)
    ((safe_groupM_iff hm (A₀ e)).mpr (hA₀ e))
  have hn₁ e := MatchingContractionClosure.SafeBinary.nonsingular (groupM_matrix_group hm)
    ((safe_groupM_iff hm (A₁ e)).mpr (hA₁ e))
  exact ⟨MatchingContractionClosure.productValue_nonzero p A₀ κ₀ hn₀ hκ₀,
    MatchingContractionClosure.productValue_nonzero p A₁ κ₁ hn₁ hκ₁⟩

end Holant.Dihedral.TwoCardLocalization
