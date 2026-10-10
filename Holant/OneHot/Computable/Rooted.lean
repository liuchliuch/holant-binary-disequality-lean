import Holant.OneHot.Computable.Reachability

/-!
# Executable rooted parent extraction

Ranks are the first successful bounded reachability round. Parent ends are found
by scanning the original finite edge table. All data definitions below compile;
proofs erase, and no classical choice is used to select parents. This is still a
Lean data algorithm, not a realization by a uniform finite-state bit machine.
-/

namespace Holant.OneHot.Computable.Graph

open Holant.OneHot.Decomposition

variable (g : Graph)

/-- Original vertices reached from the specified original root. -/
abbrev Fiber (root : g.Vertex) := {v : g.Vertex // v ∈ g.reach root g.vertices}

/-- Original edges of the component, with their original identity. -/
abbrev FiberEdge (root : g.Vertex) :=
  {e : g.Edge // g.endpoint e false ∈ g.reach root g.vertices}

def fiberRoot (root : g.Vertex) : g.Fiber root := ⟨root, g.root_mem_reach root _⟩

theorem reach_mono (root : g.Vertex) {i j : ℕ} (h : i ≤ j) :
    g.reach root i ⊆ g.reach root j := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step h ih => exact Finset.Subset.trans ih (g.reach_subset root _)

theorem endpoints_mem_iff (root : g.Vertex) (e : g.Edge) (z : Bool) :
    g.endpoint e z ∈ g.reach root g.vertices ↔
      g.endpoint e false ∈ g.reach root g.vertices := by
  cases z with
  | false => rfl
  | true =>
    simp only [g.reach_iff]
    constructor
    · intro h
      exact .trans _ _ _ h (.symm _ _ (.rel _ _ ⟨e, rfl, rfl⟩))
    · intro h
      exact .trans _ _ _ h (.rel _ _ ⟨e, rfl, rfl⟩)

def fiberEndpoint (root : g.Vertex) (e : g.FiberEdge root) (z : Bool) : g.Fiber root :=
  ⟨g.endpoint e.1 z, (g.endpoints_mem_iff root e.1 z).mpr e.2⟩

/-- Computable minimization. The following theorem bounds it by `V`; thus this
search does not run to an unbounded number encoded in an input identifier. -/
def depth (root : g.Vertex) (v : g.Fiber root) : ℕ :=
  Nat.find (show ∃ k, v.1 ∈ g.reach root k from ⟨g.vertices, v.2⟩)

theorem depth_mem (root : g.Vertex) (v : g.Fiber root) :
    v.1 ∈ g.reach root (g.depth root v) := by
  unfold depth
  exact Nat.find_spec (show ∃ k, v.1 ∈ g.reach root k from ⟨g.vertices, v.2⟩)

theorem depth_le (root : g.Vertex) (v : g.Fiber root) : g.depth root v ≤ g.vertices :=
  Nat.find_min' _ v.2

theorem depth_le_of_mem (root : g.Vertex) (v : g.Fiber root) {k : ℕ}
    (h : v.1 ∈ g.reach root k) : g.depth root v ≤ k := Nat.find_min' _ h

theorem not_mem_before_depth (root : g.Vertex) (v : g.Fiber root) {k : ℕ}
    (h : k < g.depth root v) : v.1 ∉ g.reach root k := Nat.find_min _ h

@[simp] theorem depth_eq_zero (root : g.Vertex) (v : g.Fiber root) :
    g.depth root v = 0 ↔ v = g.fiberRoot root := by
  simp only [depth, Nat.find_eq_zero, reach_zero, Finset.mem_singleton]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem parent_isSome (root : g.Vertex) (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) :
    (g.neighborRun (g.reach root (g.depth root v.1 - 1)) v.1.1).1.isSome := by
  have hp : 0 < g.depth root v.1 := Nat.pos_of_ne_zero (fun h => v.2 ((g.depth_eq_zero _ _).mp h))
  have hm := g.depth_mem root v.1
  have hd : g.depth root v.1 = (g.depth root v.1 - 1) + 1 := by omega
  rw [hd, reach_succ, mem_round] at hm
  rcases hm with h | h
  · exact (g.not_mem_before_depth root v.1 (by omega) h).elim
  · exact (g.neighborRun_spec _ _).mpr h

/-- Actual first matching original end, with an explicit finite scan. -/
def parentEnd (root : g.Vertex) (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) : g.Edge × Bool :=
  (g.neighborRun (g.reach root (g.depth root v.1 - 1)) v.1.1).1.get (g.parent_isSome root v)

theorem parentEnd_spec (root : g.Vertex) (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) :
    g.endpoint (g.parentEnd root v).1 (g.parentEnd root v).2 = v.1.1 ∧
      g.endpoint (g.parentEnd root v).1 (!(g.parentEnd root v).2) ∈
        g.reach root (g.depth root v.1 - 1) := by
  have hh : (g.neighborRun (g.reach root (g.depth root v.1 - 1)) v.1.1).1 =
      some (g.parentEnd root v) := (Option.some_get (g.parent_isSome root v)).symm
  rw [neighborRun, search_value] at hh
  have hp := List.find?_some (p := fun q : g.Edge × Bool => decide
    (g.endpoint q.1 q.2 = v.1.1 ∧
      g.endpoint q.1 (!q.2) ∈ g.reach root (g.depth root v.1 - 1))) hh
  exact of_decide_eq_true hp

/-- The selected edge stays in the same component; no new edge is introduced. -/
def fiberParentEnd (root : g.Vertex) (v : {v : g.Fiber root // v ≠ g.fiberRoot root}) :
    g.FiberEdge root × Bool :=
  (⟨(g.parentEnd root v).1, (g.endpoints_mem_iff root _ (g.parentEnd root v).2).mp
    (by rw [(g.parentEnd_spec root v).1]; exact v.1.2)⟩, (g.parentEnd root v).2)

/-- Directly consumable by the existing original-port tree extraction/evaluation
interface. It is derived from the computed table, never assumed as input. -/
def rootedSpanning (root : g.Vertex) : RootedSpanning (g.fiberEndpoint root) (g.fiberRoot root) where
  parentEnd := g.fiberParentEnd root
  child_endpoint v := Subtype.ext (g.parentEnd_spec root v).1
  depth := g.depth root
  parent_depth_lt v := by
    have hp := g.depth_le_of_mem root
      (g.fiberEndpoint root (g.fiberParentEnd root v).1 (!(g.fiberParentEnd root v).2))
      (g.parentEnd_spec root v).2
    have hn : g.depth root v.1 ≠ 0 := fun h => v.2 ((g.depth_eq_zero _ _).mp h)
    omega

/-- Each parent's rank and original edge identity satisfy the semantic evaluator's
requirements, including injectivity and exclusion of self-loops. -/
theorem parentEdge_injective (root : g.Vertex) :
    Function.Injective (g.rootedSpanning root).parentEdge :=
  (g.rootedSpanning root).parentEdge_injective

end Holant.OneHot.Computable.Graph
