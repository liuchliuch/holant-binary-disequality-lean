import Holant.EightVertex.ProductAnchor.ProductComponentsCut

/-! The source-level product-type alternative needed by Lemma 4.2, derived
from the unrestricted finite ProductFactor list itself: a complementary support
pair, or two genuine nonempty proper disjoint coordinate factors. -/
namespace Holant.EightVertex.ProductAnchor
open Holant Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A nonconstant coordinate cut yields two positive proper block arities. -/
theorem cutArity_positive_proper (C : Fin 4 → Bool)
    (h0 : ∃ i, C i = false) (h1 : ∃ i, C i = true) (v : Fin 2) :
    0 < cutArity C v ∧ cutArity C v < 4 := by
  classical
  have hyes : ∃ i, C i = finTwoEquiv v := by
    cases finTwoEquiv v
    · exact h0
    · exact h1
  have hno : ∃ i, C i ≠ finTwoEquiv v := by
    cases finTwoEquiv v
    · obtain ⟨i,hi⟩ := h1
      exact ⟨i,by simp [hi]⟩
    · obtain ⟨i,hi⟩ := h0
      exact ⟨i,by simp [hi]⟩
  constructor
  · exact Fintype.card_pos_iff.mpr (by obtain ⟨i,hi⟩ := hyes; exact ⟨⟨i,hi⟩⟩)
  · obtain ⟨i,hi⟩ := hno
    simpa [cutArity] using (Fintype.card_subtype_lt (p := fun j => C j = finTwoEquiv v) hi)

/-- Complete list-level alternative. Singleton support is permitted in the
first branch; no nonzero complementary coefficient is assumed. -/
theorem product_components (H : Signature AlgebraicComplex 4)
    (hH : H ≠ 0) (hP : Product H) :
    (∃ s : Fin 4 → Bool, ∀ x, x ≠ s → x ≠ (fun i => !(s i)) → H x = 0) ∨
    (∃ D : TensorDecomposition AlgebraicComplex 4,
      D.count = 2 ∧ (∀ i, 0 < D.arity i ∧ D.arity i < 4) ∧ D.value = H) := by
  classical
  rcases hP with hz | ⟨a,ha,ps,hformula⟩
  · exact False.elim (hH hz)
  have hs : ∃ s, H s ≠ 0 := by
    by_contra hn
    apply hH
    funext s
    by_contra hsn
    exact hn ⟨s,hsn⟩
  by_cases hc : ∀ i, FactorConnected ps 0 i
  · left
    obtain ⟨s,hs⟩ := hs
    refine ⟨s,fun x hx hy => ?_⟩
    by_contra hxn
    rw [hformula] at hs hxn
    rcases connected_support_pair a ps 0 hc s x hs hxn with h | h
    · exact hx h
    · exact hy h
  · right
    obtain ⟨j,hj⟩ := not_forall.mp hc
    let C := componentCut ps 0
    have h0 : ∃ i, C i = false := ⟨j,by simp [C,componentCut,hj]⟩
    have h1 : ∃ i, C i = true := ⟨0,componentCut_root ps 0⟩
    refine ⟨cutDecomposition a ha ps C,rfl,?_,?_⟩
    · exact fun v => cutArity_positive_proper C h0 h1 v
    · rw [cutDecomposition_value a ha ps C (componentCut_closed ps 0)]
      exact hformula.symm

end
end Holant.EightVertex.ProductAnchor
