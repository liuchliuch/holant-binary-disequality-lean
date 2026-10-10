import Holant.Platonic.RainbowLocalization.SmallCuts

/-! Pair and triple cuts force every disagreement into a four-port block. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant.Pauli.ExoticKlein MatchingCut
variable {P : Type*} [Fintype P] [DecidableEq P] {r₀ r₁ r₂ : ℕ}

/-- The necessary numerical inequality coming from a tensor-line relation.
This predicate only concerns counts of the given matching's crossing edges. -/
def CutRankTriangle (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂) : Prop :=
  ∀ S : Finset P, 2 ^ Fintype.card (Crossing M₂ (cut S)) ≤
    2 ^ Fintype.card (Crossing M₀ (cut S)) + 2 ^ Fintype.card (Crossing M₁ (cut S))

/-- An edge repeated by two points on the line must occur in the third. -/
theorem edge_of_two (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (htri : CutRankTriangle M₀ M₁ M₂) (p q : P)
    (h₀ : M₀.mate p = q) (h₁ : M₁.mate p = q) : M₂.mate p = q := by
  have hpq : p ≠ q := fun h => M₀.mate_ne_self p (h₀.trans h.symm)
  by_contra h₂
  have hh := htri {p,q}
  rw [crossing_pair_of_matched M₀ p q hpq h₀,
    crossing_pair_of_matched M₁ p q hpq h₁,
    crossing_pair_of_unmatched M₂ p q hpq h₂] at hh
  norm_num at hh

/-- Two matchings with an internal edge on a three-port cut force the third
to have an internal edge as well; otherwise its rank would be eight. -/
theorem triple_edge_of_two (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (htri : CutRankTriangle M₀ M₁ M₂) (S : Finset P) (hcard : S.card = 3)
    (h₀ : HasInternalEdge M₀ S) (h₁ : HasInternalEdge M₁ S) : HasInternalEdge M₂ S := by
  by_contra h₂
  have hh := htri S
  rw [crossing_triple_of_internal M₀ S hcard h₀,
    crossing_triple_of_internal M₁ S hcard h₁,
    crossing_triple_of_no_internal M₂ S hcard h₂] at hh
  norm_num at hh

private theorem forced_third_edge {r : ℕ} (M : Matching P r) (p q t : P)
    (hmpq : M.mate p ≠ q) (hmpt : M.mate p ≠ t)
    (hS : HasInternalEdge M {p,q,t}) : M.mate q = t := by
  obtain ⟨x,hx,hm⟩ := hS
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hm
  rcases hx with hx | hx | hx
  · subst x
    rcases hm with hm | hm | hm
    · exact (M.mate_ne_self p hm).elim
    · exact (hmpq hm).elim
    · exact (hmpt hm).elim
  · subst x
    rcases hm with hm | hm | hm
    · have he : M.mate p = q := (congrArg M.mate hm).symm.trans (M.mate_mate q)
      exact (hmpq he).elim
    · exact (M.mate_ne_self q hm).elim
    · exact hm
  · subst x
    rcases hm with hm | hm | hm
    · have he : M.mate p = t := (congrArg M.mate hm).symm.trans (M.mate_mate t)
      exact (hmpt he).elim
    · exact (congrArg M.mate hm).symm.trans (M.mate_mate t)
    · exact (M.mate_ne_self t hm).elim

/-- At each disagreement, the three matching involutions are exactly the
three perfect matchings of the four displayed ports.  In particular there
cannot be a longer exceptional alternating cycle. -/
theorem local_four_port_relations
    (M₀ : Matching P r₀) (M₁ : Matching P r₁) (M₂ : Matching P r₂)
    (h₂ : CutRankTriangle M₀ M₁ M₂) (h₁ : CutRankTriangle M₀ M₂ M₁)
    (h₀ : CutRankTriangle M₁ M₂ M₀) (p : P)
    (hne : M₀.mate p ≠ M₁.mate p) :
    M₂.mate p ≠ M₀.mate p ∧ M₂.mate p ≠ M₁.mate p ∧
      M₂.mate (M₀.mate p) = M₁.mate p ∧
      M₁.mate (M₀.mate p) = M₂.mate p ∧
      M₀.mate (M₁.mate p) = M₂.mate p := by
  have h₂₀ : M₂.mate p ≠ M₀.mate p := by
    intro h
    exact hne (edge_of_two M₀ M₂ M₁ h₁ p (M₀.mate p) rfl h).symm
  have h₂₁ : M₂.mate p ≠ M₁.mate p := by
    intro h
    exact hne (edge_of_two M₁ M₂ M₀ h₀ p (M₁.mate p) rfl h)
  have hcard (u v : P) (hu : u ≠ p) (hv : v ≠ p) (huv : u ≠ v) :
      ({p,u,v} : Finset P).card = 3 := by
    simp [hu, hv, huv, Ne.symm hu, Ne.symm hv]
  have hedge {r : ℕ} (M : Matching P r) (v : P) : HasInternalEdge M {p,M.mate p,v} :=
    ⟨p,by simp,by simp⟩
  have hedge' {r : ℕ} (M : Matching P r) (v : P) : HasInternalEdge M {p,v,M.mate p} :=
    ⟨p,by simp,by simp⟩
  refine ⟨h₂₀,h₂₁,?_,?_,?_⟩
  · apply forced_third_edge M₂ p (M₀.mate p) (M₁.mate p) h₂₀ h₂₁
    exact triple_edge_of_two M₀ M₁ M₂ h₂ _
      (hcard _ _ (M₀.mate_ne_self p) (M₁.mate_ne_self p) hne)
      (hedge M₀ _) (hedge' M₁ _)
  · apply forced_third_edge M₁ p (M₀.mate p) (M₂.mate p) hne.symm h₂₁.symm
    exact triple_edge_of_two M₀ M₂ M₁ h₁ _
      (hcard _ _ (M₀.mate_ne_self p) (M₂.mate_ne_self p) h₂₀.symm)
      (hedge M₀ _) (hedge' M₂ _)
  · apply forced_third_edge M₀ p (M₁.mate p) (M₂.mate p) hne h₂₀.symm
    exact triple_edge_of_two M₁ M₂ M₀ h₀ _
      (hcard _ _ (M₁.mate_ne_self p) (M₂.mate_ne_self p) h₂₁.symm)
      (hedge M₁ _) (hedge' M₂ _)

end Holant.Platonic.RainbowLocalization
