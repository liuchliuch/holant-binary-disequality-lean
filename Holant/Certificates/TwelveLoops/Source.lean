import Holant.Certificates.TwelveLoops.Counts
import Holant.Certificates.TwelveLoops.Transfers

/-! Proposition A.1: the complete deterministic partition and exact exit
semantics. Literal loop formulas and equality-mediated contraction identities
are proved separately, rather than postulated as an interface hypothesis. -/
namespace Holant.Certificates.TwelveLoops

theorem source_a0 (s : State) : embed (a s 0)=1 := by
  norm_num [a,alpha,fourthRoot,embed]

theorem source_roots_nonzero (s : State) (j : Fin 4) :
    embed (a s j)≠0 ∧ embed (b s j)≠0 := by
  have hr (k : Fin 4) : embed (fourthRoot k)≠0 := by
    fin_cases k <;> norm_num [fourthRoot,embed]
  exact ⟨hr _,hr _⟩

theorem source_table_values (s : State) (j : Fin 4) :
    oddTable (fun k => embed (a s k)) (fun k => embed (b s k)) (singleWord j)=embed (a s j) ∧
    oddTable (fun k => embed (a s k)) (fun k => embed (b s k)) (complementWord j)=embed (b s j) :=
  ⟨oddTable_single _ _ j,oddTable_complement _ _ j⟩

theorem rankOne_exit (s : State) (h : classify s=.rankOne) :
    ∃ p∈loopPairs s, (transfer p.1 p.2).rank=1 ∧ (offMatrix p.1 p.2).rank=1 := by
  obtain ⟨p,hp,hh⟩ := (rankOne_iff s).mp h
  refine ⟨p,hp,rankOneTest_rank p.1 p.2 ?_⟩
  rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp [rankOneTest,h₁,h₂]

theorem infiniteOrder_exit (s : State) (h : classify s=.infiniteOrder) :
    ∃ p∈loopPairs s, p.1≠(0,0) ∧ p.2≠(0,0) ∧
      ¬ ProjectivelyFinite (transfer p.1 p.2) := by
  obtain ⟨_,p,hp,hh⟩ := (infiniteOrder_iff s).mp h
  have hne : p.1≠(0,0) ∧ p.2≠(0,0) ∧ gnorm p.1≠gnorm p.2 := by
    simpa [infiniteTest,and_assoc] using hh
  exact ⟨p,hp,hne.1,hne.2.1,norm_mismatch_infinite p.1 p.2 hh⟩

theorem remaining_keeps_zeros (s : State) (h : classify s=.remaining) :
    ∀ p∈loopPairs s, (p.1=(0,0) ∧ p.2=(0,0)) ∨
      (p.1≠(0,0) ∧ p.2≠(0,0) ∧ ProjectivelyFinite (transfer p.1 p.2)) := by
  intro p hp
  rcases remaining_fourth_root s h p hp with hz | hn
  · exact Or.inl hz
  · exact Or.inr ⟨hn.1,hn.2.1,transfer_finite_of_fourth_root p.1 p.2 hn.2.1 hn.2.2⟩

/-- Every one of the literal4^7 states receives exactly the priority-ordered
source route, with genuine matrix-rank and projective-order conclusions. -/
theorem deterministic_twelve_loop_test :
    Fintype.card State=16384 ∧ routeCount .rankOne=15792 ∧
    routeCount .infiniteOrder=224 ∧ routeCount .remaining=368 ∧
    (∀ s, classify s=.rankOne →
      ∃ p∈loopPairs s, (transfer p.1 p.2).rank=1 ∧ (offMatrix p.1 p.2).rank=1) ∧
    (∀ s, classify s=.infiniteOrder →
      ∃ p∈loopPairs s, p.1≠(0,0) ∧ p.2≠(0,0) ∧ ¬ ProjectivelyFinite (transfer p.1 p.2)) ∧
    (∀ s, classify s=.remaining → ∀ p∈loopPairs s,
      (p.1=(0,0) ∧ p.2=(0,0)) ∨
      (p.1≠(0,0) ∧ p.2≠(0,0) ∧ ProjectivelyFinite (transfer p.1 p.2))) :=
  ⟨deterministic_partition.1,deterministic_partition.2.1,
    deterministic_partition.2.2.1,deterministic_partition.2.2.2,
    rankOne_exit,infiniteOrder_exit,remaining_keeps_zeros⟩

end Holant.Certificates.TwelveLoops
