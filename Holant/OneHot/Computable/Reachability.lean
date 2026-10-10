import Holant.OneHot.Computable.Incidence
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

/-!
# Bounded executable reachability on an explicit edge table

The graph stores a finite list of endpoint pairs. Vertex and edge IDs are indexes
into actual stored lists; IDs are never used as allocation bounds. A round scans
all vertices and the explicit list of oriented original edges. After `V` rounds
it equals graph reachability, including loops, parallel edges and isolated vertices.
The instrumented counter counts original-end predicate tests, not machine steps.
-/

namespace Holant.OneHot.Computable

open Holant.OneHot.Decomposition

/-- A concrete finite table, retaining every edge separately and in order. -/
structure Graph where
  vertices : ℕ
  edges : List (Fin vertices × Fin vertices)
  deriving DecidableEq

namespace Graph

abbrev Vertex (g : Graph) := Fin g.vertices
abbrev Edge (g : Graph) := Fin g.edges.length

def endpoint (g : Graph) (e : g.Edge) (z : Bool) : g.Vertex :=
  if z then (g.edges.get e).2 else (g.edges.get e).1

/-- Exactly two oriented occurrences for every original edge, never pairs of
vertices or a power set of potential edges. -/
def ends (g : Graph) : List (g.Edge × Bool) :=
  (List.finRange g.edges.length).flatMap fun e => [(e, false), (e, true)]

@[simp] theorem ends_length (g : Graph) : g.ends.length = 2 * g.edges.length := by
  simp [ends, List.length_flatMap, List.sum_replicate, Nat.mul_comm]

@[simp] theorem mem_ends (g : Graph) (q : g.Edge × Bool) : q ∈ g.ends := by
  rcases q with ⟨e, z⟩
  apply List.mem_flatMap.mpr
  refine ⟨e, List.mem_finRange _, ?_⟩
  cases z <;> simp

/-- One executable finite scan for a neighbor in the previous layer. -/
def neighborRun (g : Graph) (s : Finset g.Vertex) (v : g.Vertex) :
    Option (g.Edge × Bool) × ℕ :=
  search (fun q => decide (g.endpoint q.1 q.2 = v ∧ g.endpoint q.1 (!q.2) ∈ s)) g.ends

theorem neighborRun_spec (g : Graph) (s : Finset g.Vertex) (v : g.Vertex) :
    (g.neighborRun s v).1.isSome ↔
      ∃ q : g.Edge × Bool, g.endpoint q.1 q.2 = v ∧ g.endpoint q.1 (!q.2) ∈ s := by
  simp [neighborRun, search_value, List.find?_isSome]

theorem neighborRun_work_le (g : Graph) (s : Finset g.Vertex) (v : g.Vertex) :
    (g.neighborRun s v).2 ≤ 2 * g.edges.length := by
  simpa [neighborRun] using search_work_le
    (fun q => decide (g.endpoint q.1 q.2 = v ∧ g.endpoint q.1 (!q.2) ∈ s)) g.ends

/-- The returned state and counter use the same list of actual scan results. -/
def roundRun (g : Graph) (s : Finset g.Vertex) : Finset g.Vertex × ℕ :=
  let scans := (List.finRange g.vertices).map fun v => (v, g.neighborRun s v)
  (s ∪ (scans.filterMap fun x => if x.2.1.isSome then some x.1 else none).toFinset,
    (scans.map fun x => x.2.2).sum)

def round (g : Graph) (s : Finset g.Vertex) : Finset g.Vertex := (g.roundRun s).1

@[simp] theorem mem_round (g : Graph) (s : Finset g.Vertex) (v : g.Vertex) :
    v ∈ g.round s ↔ v ∈ s ∨
      ∃ q : g.Edge × Bool, g.endpoint q.1 q.2 = v ∧ g.endpoint q.1 (!q.2) ∈ s := by
  simp only [round, roundRun, Finset.mem_union, List.mem_toFinset, List.mem_filterMap,
    List.mem_map]
  constructor
  · rintro (h | ⟨_, ⟨u, hu, rfl⟩, hv⟩)
    · exact Or.inl h
    · split at hv
      · cases hv
        exact Or.inr ((g.neighborRun_spec s u).mp ‹_›)
      · contradiction
  · rintro (h | ⟨q, hq⟩)
    · exact Or.inl h
    · right
      refine ⟨(v, g.neighborRun s v), ⟨v, List.mem_finRange _, rfl⟩, ?_⟩
      have h := (g.neighborRun_spec s v).mpr ⟨q, hq⟩
      simp [h]

theorem subset_round (g : Graph) (s : Finset g.Vertex) : s ⊆ g.round s :=
  fun _ h => (g.mem_round _ _).mpr (Or.inl h)

theorem round_work_le (g : Graph) (s : Finset g.Vertex) :
    (g.roundRun s).2 ≤ 2 * g.vertices * g.edges.length := by
  dsimp [roundRun]
  rw [List.map_map]
  have h : ∀ v ∈ List.finRange g.vertices,
      (g.neighborRun s v).2 ≤ 2 * g.edges.length := fun v _ => g.neighborRun_work_le s v
  have bound (xs : List g.Vertex) :
      (xs.map fun v => (g.neighborRun s v).2).sum ≤ xs.length * (2 * g.edges.length) := by
    induction xs with
    | nil => simp
    | cons v xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      have hv := g.neighborRun_work_le s v
      omega
  simpa [Function.comp_def, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound (List.finRange g.vertices)

/-- Structural recursion supplies termination on every finite table. -/
def reachRun (g : Graph) (root : g.Vertex) : ℕ → Finset g.Vertex × ℕ
  | 0 => ({root}, 0)
  | k + 1 => let prev := g.reachRun root k
             let next := g.roundRun prev.1
             (next.1, prev.2 + next.2)

def reach (g : Graph) (root : g.Vertex) (k : ℕ) : Finset g.Vertex := (g.reachRun root k).1

@[simp] theorem reach_zero (g : Graph) (root : g.Vertex) : g.reach root 0 = {root} := rfl
@[simp] theorem reach_succ (g : Graph) (root : g.Vertex) (k : ℕ) :
    g.reach root (k + 1) = g.round (g.reach root k) := rfl

theorem reach_subset (g : Graph) (root : g.Vertex) (k : ℕ) :
    g.reach root k ⊆ g.reach root (k + 1) := g.subset_round _

theorem root_mem_reach (g : Graph) (root : g.Vertex) (k : ℕ) : root ∈ g.reach root k := by
  induction k with
  | zero => simp
  | succ k ih => exact g.reach_subset root k ih

theorem reach_work_le (g : Graph) (root : g.Vertex) (k : ℕ) :
    (g.reachRun root k).2 ≤ k * (2 * g.vertices * g.edges.length) := by
  induction k with
  | zero => simp [reachRun]
  | succ k ih =>
    have h := g.round_work_le (g.reach root k)
    change (g.reachRun root k).2 + (g.roundRun (g.reach root k)).2 ≤ _
    calc
      _ ≤ k * (2 * g.vertices * g.edges.length) + 2 * g.vertices * g.edges.length :=
        Nat.add_le_add ih h
      _ = _ := by simp [Nat.add_mul]

private theorem stable_or_large (g : Graph) (root : g.Vertex) (k : ℕ) :
    g.round (g.reach root k) = g.reach root k ∨ k + 1 ≤ (g.reach root k).card := by
  induction k with
  | zero => right; simp
  | succ k ih =>
    by_cases h : g.round (g.reach root k) = g.reach root k
    · left
      simp only [reach_succ, h]
    · right
      have hp : k + 1 ≤ (g.reach root k).card := ih.resolve_left h
      have hc : (g.reach root k).card < (g.reach root (k + 1)).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨g.reach_subset root k, by
          simpa only [reach_succ, ne_eq, eq_comm] using h⟩)
      omega

/-- `V` rounds suffice without enumerating paths or subsets of the vertex set. -/
theorem reach_stable (g : Graph) (root : g.Vertex) :
    g.round (g.reach root g.vertices) = g.reach root g.vertices := by
  rcases g.stable_or_large root g.vertices with h | h
  · exact h
  · have hc := Finset.card_le_univ (g.reach root g.vertices)
    simp only [Fintype.card_fin] at hc
    omega

theorem reach_sound (g : Graph) (root : g.Vertex) (k : ℕ) (v : g.Vertex)
    (hv : v ∈ g.reach root k) : Relation.EqvGen (Link g.endpoint) root v := by
  induction k generalizing v with
  | zero =>
    have hh : v = root := by simpa using hv
    subst v
    exact .refl _
  | succ k ih =>
    rw [reach_succ, mem_round] at hv
    rcases hv with hv | ⟨⟨e, z⟩, rfl, hp⟩
    · exact ih v hv
    · apply Relation.EqvGen.trans _ _ _ (ih _ hp)
      cases z
      · exact .symm _ _ (.rel _ _ ⟨e, rfl, rfl⟩)
      · exact .rel _ _ ⟨e, rfl, rfl⟩

private theorem stable_edge (g : Graph) (root : g.Vertex) (e : g.Edge) (z : Bool)
    (h : g.endpoint e (!z) ∈ g.reach root g.vertices) :
    g.endpoint e z ∈ g.reach root g.vertices := by
  rw [← g.reach_stable root]
  exact (g.mem_round _ _).mpr (Or.inr ⟨(e, z), rfl, h⟩)

/-- Exact connectivity on the original edge-labelled multigraph. -/
theorem reach_iff (g : Graph) (root v : g.Vertex) :
    v ∈ g.reach root g.vertices ↔ Relation.EqvGen (Link g.endpoint) root v := by
  constructor
  · exact g.reach_sound root g.vertices v
  · intro h
    have transfer : ∀ u w, Relation.EqvGen (Link g.endpoint) u w →
        (u ∈ g.reach root g.vertices ↔ w ∈ g.reach root g.vertices) := by
      intro u w h
      induction h with
      | rel u w h =>
        rcases h with ⟨e, rfl, rfl⟩
        exact ⟨g.stable_edge root e true, g.stable_edge root e false⟩
      | refl u => rfl
      | symm u v _ ih => exact ih.symm
      | trans u v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (transfer root v h).mp (g.root_mem_reach root _)

end Graph
end Holant.OneHot.Computable
