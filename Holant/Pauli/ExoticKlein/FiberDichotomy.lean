import Holant.Pauli.ExoticKlein.FiberCardCounts
import Holant.Pauli.ExoticKlein.FiberFactor

/-! Full fixed-ruling fiber dichotomy. Actual proper cards force all four
coefficients to survive and every original edge label map to be a permutation,
unless the original tensor has a genuine positive-arity tensor factor. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
open MatchingCard
namespace Fiber
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

theorem label_predicate_of_card_four (p : Label → Prop) [DecidablePred p]
    (hc : Fintype.card {a : Label // p a} = 4) : ∀ a, p a := by
  have hb := (Fintype.bijective_iff_injective_and_card (fun a : {a : Label // p a} => a.val)).mpr
    ⟨Subtype.val_injective,hc.trans card_label.symm⟩
  intro a
  obtain ⟨b,hb⟩ := hb.2 a
  exact hb ▸ b.property

theorem all_weights_nonzero (M : Matching P r) (hr : 3 ≤ r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (distinguished : Fin r)
    (hlabel : ∀ a, labels a distinguished = a) (hs : PairSafe (tensor M weight labels))
    (hn : tensor M weight labels ≠ 0) (hp : ¬ HasProperTensorFactor (tensor M weight labels)) :
    ∀ a, weight a ≠ 0 := by
  classical
  rcases proper_card_live_count M hr weight labels distinguished hlabel hs with hc | hc | hc
  · exfalso
    apply hn
    apply (zero_iff M weight labels distinguished hlabel).mpr
    intro a
    by_contra ha
    have hpos : 0 < Fintype.card {a : Label // weight a ≠ 0} :=
      Fintype.card_pos_iff.mpr ⟨⟨a,ha⟩⟩
    omega
  · obtain ⟨a,ha⟩ := Fintype.card_eq_one_iff.mp hc
    exfalso
    apply hp
    apply constant_edge_factor M (by omega) weight labels distinguished a.val hn
    intro b hb
    rw [hlabel]
    exact congrArg Subtype.val (ha ⟨b,hb⟩)
  · exact label_predicate_of_card_four _ hc

theorem all_label_maps_bijective (M : Matching P r) (hr : 3 ≤ r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (distinguished : Fin r)
    (hlabel : ∀ a, labels a distinguished = a) (hs : PairSafe (tensor M weight labels))
    (hn : tensor M weight labels ≠ 0) (hp : ¬ HasProperTensorFactor (tensor M weight labels))
    (hw : ∀ a, weight a ≠ 0) : ∀ e, Function.Bijective (fun a => labels a e) := by
  classical
  intro e
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,rfl⟩
  intro a b hab
  by_cases hde : distinguished = e
  · subst e
    simpa only [hlabel] using hab
  rcases edge_fiber_count M weight labels distinguished e hde hlabel hs (labels a e) with hc | hc | hc
  · have hpos : 0 < Fintype.card {j : Label // weight j ≠ 0 ∧ labels j e = labels a e} :=
      Fintype.card_pos_iff.mpr ⟨⟨a,hw a,rfl⟩⟩
    omega
  · obtain ⟨j,hj⟩ := Fintype.card_eq_one_iff.mp hc
    exact congrArg Subtype.val ((hj ⟨a,hw a,rfl⟩).trans (hj ⟨b,hw b,hab.symm⟩).symm)
  · have hc' := label_predicate_of_card_four _ hc
    exact False.elim (hp (constant_edge_factor M (by omega) weight labels e (labels a e) hn
      (fun j _ => (hc' j).2)))

/-- Source Lemma 8.7 in full original matching coordinates. -/
theorem dichotomy (M : Matching P r) (hr : 3 ≤ r) (weight : Label → ℂ)
    (labels : Label → Fin r → Label) (distinguished : Fin r)
    (hlabel : ∀ a, labels a distinguished = a) (hs : PairSafe (tensor M weight labels))
    (hn : tensor M weight labels ≠ 0) (hp : ¬ HasProperTensorFactor (tensor M weight labels)) :
    (∀ a, weight a ≠ 0) ∧ ∀ e, Function.Bijective (fun a => labels a e) := by
  have hw := all_weights_nonzero M hr weight labels distinguished hlabel hs hn hp
  exact ⟨hw,all_label_maps_bijective M hr weight labels distinguished hlabel hs hn hp hw⟩

end Fiber
end
end Holant.Pauli.ExoticKlein
