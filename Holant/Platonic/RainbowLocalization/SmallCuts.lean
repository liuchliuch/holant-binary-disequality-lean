import Holant.Platonic.RainbowLocalization.CutCoordinates

/-! Crossing counts for two- and three-port cuts, computed from actual mates. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization.MatchingCut
open Holant.Pauli.ExoticKlein
variable {P : Type*} [Fintype P] [DecidableEq P] {r : ℕ}

def cut (S : Finset P) : P → Bool := fun p => decide (p ∈ S)

@[simp] theorem cut_true (S : Finset P) (p : P) : cut S p = true ↔ p ∈ S := by
  simp [cut]

@[simp] theorem cut_false (S : Finset P) (p : P) : cut S p = false ↔ p ∉ S := by
  simp [cut]

theorem side_cut_card (S : Finset P) : Fintype.card (Side (cut S) true) = S.card := by
  let e : Side (cut S) true ≃ S := Equiv.subtypeEquivRight (fun p => cut_true S p)
  rw [Fintype.card_congr e, Fintype.card_coe]

theorem side_cut_compl_card (S : Finset P) :
    Fintype.card (Side (cut S) false) = Fintype.card P - S.card := by
  let e : Side (cut S) false ≃ (Sᶜ : Finset P) :=
    Equiv.subtypeEquivRight (fun p => by simp)
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_compl]

def HasInternalEdge (M : Matching P r) (S : Finset P) : Prop :=
  ∃ p ∈ S, M.mate p ∈ S

theorem internal_nonempty_iff (M : Matching P r) (S : Finset P) :
    Nonempty (Internal M (cut S) true) ↔ HasInternalEdge M S := by
  constructor
  · rintro ⟨e⟩
    refine ⟨M.ports (e.val,false), (cut_true S _).mp e.property.1, ?_⟩
    rw [M.mate_port]
    exact (cut_true S _).mp e.property.2
  · rintro ⟨p,hp,hm⟩
    obtain ⟨⟨e,t⟩,rfl⟩ := M.ports.surjective p
    rw [M.mate_port] at hm
    refine ⟨⟨e,?_⟩⟩
    cases t
    · exact ⟨(cut_true S _).mpr hp, (cut_true S _).mpr hm⟩
    · exact ⟨(cut_true S _).mpr hm, (cut_true S _).mpr hp⟩

theorem cut_card (M : Matching P r) (S : Finset P) :
    S.card = 2 * Fintype.card (Internal M (cut S) true) + Fintype.card (Crossing M (cut S)) := by
  rw [← side_cut_card S]
  exact side_card M (cut S) true

/-- A cut containing no matching edge has one crossing edge per port. -/
theorem crossing_eq_card_of_no_internal (M : Matching P r) (S : Finset P)
    (hS : ¬ HasInternalEdge M S) : Fintype.card (Crossing M (cut S)) = S.card := by
  have hz : Fintype.card (Internal M (cut S) true) = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun e => hS ((internal_nonempty_iff M S).mp ⟨e⟩)⟩
  simpa only [hz, mul_zero, zero_add] using (cut_card M S).symm

theorem pair_internal_iff (M : Matching P r) (p q : P) (hpq : p ≠ q) :
    HasInternalEdge M {p,q} ↔ M.mate p = q := by
  constructor
  · rintro ⟨v,hv,hm⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hm
    rcases hv with hv | hv
    · subst v
      exact hm.resolve_left (M.mate_ne_self p)
    · subst v
      rcases hm with hm | hm
      · exact (congrArg M.mate hm).symm.trans (M.mate_mate q)
      · exact (M.mate_ne_self q hm).elim
  · intro h
    exact ⟨p,by simp,by simp [h]⟩

theorem crossing_pair_of_matched (M : Matching P r) (p q : P) (hpq : p ≠ q)
    (hm : M.mate p = q) : Fintype.card (Crossing M (cut {p,q})) = 0 := by
  have hc : ({p,q} : Finset P).card = 2 := by simp [hpq]
  have hi : 0 < Fintype.card (Internal M (cut {p,q}) true) :=
    Fintype.card_pos_iff.mpr ((internal_nonempty_iff M _).mpr ((pair_internal_iff M p q hpq).mpr hm))
  have he := cut_card M {p,q}
  omega

theorem crossing_pair_of_unmatched (M : Matching P r) (p q : P) (hpq : p ≠ q)
    (hm : M.mate p ≠ q) : Fintype.card (Crossing M (cut {p,q})) = 2 := by
  rw [crossing_eq_card_of_no_internal M _ (fun h => hm ((pair_internal_iff M p q hpq).mp h))]
  simp [hpq]

/-- Any matching edge in a three-port cut leaves exactly one crossing edge. -/
theorem crossing_triple_of_internal (M : Matching P r) (S : Finset P) (hcard : S.card = 3)
    (hS : HasInternalEdge M S) : Fintype.card (Crossing M (cut S)) = 1 := by
  have hi : 0 < Fintype.card (Internal M (cut S) true) :=
    Fintype.card_pos_iff.mpr ((internal_nonempty_iff M S).mpr hS)
  have he := cut_card M S
  omega

theorem crossing_triple_of_no_internal (M : Matching P r) (S : Finset P) (hcard : S.card = 3)
    (hS : ¬ HasInternalEdge M S) : Fintype.card (Crossing M (cut S)) = 3 := by
  rw [crossing_eq_card_of_no_internal M S hS,hcard]

/-- An even side has an even number of crossing edges. -/
theorem crossing_even_of_side_even (M : Matching P r) (S : Finset P) (hS : Even S.card) :
    Even (Fintype.card (Crossing M (cut S))) := by
  rw [cut_card M S] at hS
  exact (Nat.even_add.mp hS).mp (even_two_mul _)

end Holant.Platonic.RainbowLocalization.MatchingCut
