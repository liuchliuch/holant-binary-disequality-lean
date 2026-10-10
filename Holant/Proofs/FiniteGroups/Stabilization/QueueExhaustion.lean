import Holant.Proofs.FiniteGroups.Stabilization.FrozenWorklist
import Mathlib.Logic.Relation


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

noncomputable section
variable {L : Type*} [Field L]

def OpenFrontier (W : Multiset (TreeOccurrence L)) : Prop := ∀ t ∈ W, 2 ≤ t.1.1

theorem openTree_frontier (t : TreeOccurrence L) : OpenFrontier (openTree t) := by
  intro u hu
  by_cases h : 2 ≤ t.1.1
  · have he : u = t := by simpa [openTree, h] using hu
    simpa only [he] using h
  · simp [openTree, h] at hu

theorem treeStep_frontier {W V : Multiset (TreeOccurrence L)} (h : TreeStep W V)
    (hV : OpenFrontier V) : OpenFrontier W := by
  cases h with
  | leaf f hp hn W => exact fun u hu => hV u (Multiset.mem_cons_of_mem hu)
  | split s ta tb W =>
      intro u hu
      rcases Multiset.mem_add.mp hu with hu | hu
      · rcases Multiset.mem_add.mp hu with ha | hb
        · exact openTree_frontier _ u ha
        · exact openTree_frontier _ u hb
      · exact hV u (Multiset.mem_cons_of_mem hu)

theorem treeStep_exists (W : Multiset (TreeOccurrence L)) (hW : OpenFrontier W)
    (hne : W ≠ 0) : ∃ V, TreeStep V W := by
  obtain ⟨⟨f, t⟩, ht⟩ := Multiset.exists_mem_of_ne_zero hne
  have hn := hW ⟨f, t⟩ ht
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem ht
  cases t with
  | leaf f hp => exact ⟨rest, .leaf f hp hn rest⟩
  | split s ta tb => exact ⟨_, .split s ta tb rest⟩

namespace FrozenQueue

variable {κ : Type*} [DecidableEq κ] {U : Finset κ}

def Valid (q : FrozenQueue L U) : Prop := ∀ k ∈ q.todo, OpenFrontier (q.work k)

theorem initial_valid (U : Finset κ) (root : κ → TreeOccurrence L) :
    (initial U root).Valid := fun k _ => openTree_frontier (root k)

theorem step_valid {q' q : FrozenQueue L U} (h : Step q' q) (hq : q.Valid) : q'.Valid := by
  cases h with
  | finish q k hk he =>
      intro j hj
      exact hq j (Finset.mem_of_mem_erase hj)
  | process q k hk W he =>
      intro j hj
      by_cases hjk : j = k
      · subst j
        change OpenFrontier (Function.update q.work k W k)
        rw [Function.update_self]
        exact treeStep_frontier he (hq k hk)
      · change OpenFrontier (Function.update q.work k W j)
        rw [Function.update_of_ne hjk]
        exact hq j hj

/-- Progress is proved from the finite tree's constructors, not postulated. -/
theorem step_exists (q : FrozenQueue L U) (hq : q.Valid) (hne : q.todo ≠ ∅) :
    ∃ q', Step q' q := by
  obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  by_cases hz : q.work k = 0
  · exact ⟨q.finish k, .finish q k hk hz⟩
  · obtain ⟨W, hW⟩ := treeStep_exists (q.work k) (hq k hk) hz
    exact ⟨q.process k W, .process q k hk W hW⟩

abbrev Runs (q q' : FrozenQueue L U) : Prop :=
  Relation.ReflTransGen (fun a b => Step b a) q q'

theorem runs_todo_subset {q q' : FrozenQueue L U} (h : Runs q q') : q'.todo ⊆ q.todo := by
  induction h with
  | refl => exact fun _ h => h
  | tail hrun hstep ih => exact (step_todo_subset hstep).trans ih

theorem runs_done_subset {q q' : FrozenQueue L U} (h : Runs q q') : q.done ⊆ q'.done := by
  intro k hk
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hk).1,
    fun hn => (Finset.mem_sdiff.mp hk).2 (runs_todo_subset h hn)⟩

/-- A completed token never returns in any later finite run. -/
theorem completed_never_reopens {q q' : FrozenQueue L U} (h : Runs q q')
    {k : κ} (hk : k ∈ q.done) : k ∉ q'.todo :=
  (Finset.mem_sdiff.mp (runs_done_subset h hk)).2

theorem done_eq_universe_of_exhausted (q : FrozenQueue L U) (he : q.todo = ∅) : q.done = U := by
  simp [done, he]

/-- The local frozen worklist always has a finite run ending with no unfinished
token.  Token completion only occurs after its frontier is empty. -/
theorem exists_exhausted (q : FrozenQueue L U) (hq : q.Valid) :
    ∃ q', Runs q q' ∧ q'.todo = ∅ := by
  refine step_wellFounded.induction q (C := fun q => q.Valid → ∃ q', Runs q q' ∧ q'.todo = ∅) ?_ hq
  intro q ih hv
  by_cases he : q.todo = ∅
  · exact ⟨q, .refl, he⟩
  · obtain ⟨q', hstep⟩ := step_exists q hv he
    obtain ⟨q'', hrun, hempty⟩ := ih q' hstep (step_valid hstep hv)
    exact ⟨q'', (show Runs q q' from Relation.ReflTransGen.single hstep).trans hrun, hempty⟩

theorem initial_exhausts (U : Finset κ) (root : κ → TreeOccurrence L) :
    ∃ q', Runs (initial U root) q' ∧ q'.todo = ∅ :=
  exists_exhausted (initial U root) (initial_valid U root)

end FrozenQueue
end
end Holant.LocalDrafts.FinitePGL2.Stabilization
