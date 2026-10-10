import Holant.OneHot.Decomposition.Components
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Sum

/-!
# Rooted spanning trees extracted from actual multigraphs

The construction chooses shortest walks in the original edge-labelled multigraph.
A parent is an original edge and one of its two endpoint occurrences. Strict
rank descent and injectivity are proved, rather than supplied as decomposition
hypotheses. The construction is semantic and makes no algorithmic cost claim.
-/

namespace Holant.OneHot.Decomposition

variable {V E : Type*} (endpoint : E → Bool → V)

/-- The generating adjacency retains the identity of its original edge. -/
def Link (u v : V) : Prop := ∃ e, endpoint e false = u ∧ endpoint e true = v

/-- A walk stores an orientation of every traversed original edge. -/
inductive Walk : V → V → ℕ → Prop
  | nil (v) : Walk v v 0
  | snoc {u : V} {n : ℕ} (e : E) (b : Bool) :
      Walk u (endpoint e b) n → Walk u (endpoint e (!b)) (n + 1)

namespace Walk

variable {endpoint}

theorem append {u v w : V} {n m : ℕ}
    (p : Walk endpoint u v n) (q : Walk endpoint v w m) :
    Walk endpoint u w (n + m) := by
  induction q with
  | nil => simpa using p
  | snoc e b q ih => simpa [Nat.add_assoc] using Walk.snoc e b ih

theorem reverse {u v : V} {n : ℕ} (p : Walk endpoint u v n) :
    Walk endpoint v u n := by
  induction p with
  | nil => exact .nil _
  | snoc e b p ih =>
    have h : Walk endpoint (endpoint e (!b)) (endpoint e b) 1 := by
      simpa using Walk.snoc e (!b) (Walk.nil (endpoint e (!b)))
    simpa [Nat.add_comm] using h.append ih

@[simp] theorem zero_iff {u v : V} : Walk endpoint u v 0 ↔ u = v := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

theorem exists_last {u v : V} {n : ℕ} (p : Walk endpoint u v (n + 1)) :
    ∃ e b, v = endpoint e (!b) ∧ Walk endpoint u (endpoint e b) n := by
  cases p with
  | snoc e b p => exact ⟨e, b, rfl, p⟩

theorem reachable {u v : V} {n : ℕ} (p : Walk endpoint u v n) :
    Relation.EqvGen (Link endpoint) u v := by
  induction p with
  | nil => exact .refl _
  | snoc e b p ih =>
    apply Relation.EqvGen.trans _ _ _ ih
    cases b with
    | false => exact .rel _ _ ⟨e, rfl, rfl⟩
    | true => exact .symm _ _ (.rel _ _ ⟨e, rfl, rfl⟩)

end Walk

/-- The chosen walk notion is precisely the original graph connectivity. -/
theorem reachable_iff_exists_walk (u v : V) :
    Relation.EqvGen (Link endpoint) u v ↔ ∃ n, Walk endpoint u v n := by
  constructor
  · intro h
    induction h with
    | rel u v h =>
      rcases h with ⟨e, rfl, rfl⟩
      exact ⟨1, Walk.snoc e false (Walk.nil _)⟩
    | refl u => exact ⟨0, Walk.nil _⟩
    | symm u v h ih =>
      rcases ih with ⟨n, p⟩
      exact ⟨n, p.reverse⟩
    | trans u v w h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨n, p⟩
      rcases ih₂ with ⟨m, q⟩
      exact ⟨n + m, p.append q⟩
  · rintro ⟨n, p⟩
    exact p.reachable

/-- A rooted spanning structure uses one original endpoint for each non-root
vertex. Its opposite endpoint is its parent, at a strictly smaller rank. -/
structure RootedSpanning (root : V) where
  parentEnd : {v : V // v ≠ root} → E × Bool
  child_endpoint : ∀ v, endpoint (parentEnd v).1 (parentEnd v).2 = v.1
  depth : V → ℕ
  parent_depth_lt : ∀ v,
    depth (endpoint (parentEnd v).1 (!(parentEnd v).2)) < depth v.1

variable (root : V) (connected : ∀ v, Relation.EqvGen (Link endpoint) root v)

/-- Shortest-walk length in the original graph, with loops and parallel edges. -/
noncomputable def distance (v : V) : ℕ := by
  classical
  exact Nat.find ((reachable_iff_exists_walk endpoint root v).mp (connected v))

private theorem distance_walk (v : V) :
    Walk endpoint root v (distance endpoint root connected v) := by
  classical
  exact Nat.find_spec ((reachable_iff_exists_walk endpoint root v).mp (connected v))

private theorem distance_le {v : V} {n : ℕ} (p : Walk endpoint root v n) :
    distance endpoint root connected v ≤ n := by
  classical
  exact Nat.find_min' ((reachable_iff_exists_walk endpoint root v).mp (connected v)) p

/-- A shortest nonempty walk yields an actual predecessor edge with smaller rank. -/
theorem exists_parentEnd (v : {v : V // v ≠ root}) :
    ∃ q : E × Bool, endpoint q.1 q.2 = v.1 ∧
      distance endpoint root connected (endpoint q.1 (!q.2)) <
        distance endpoint root connected v.1 := by
  have p := distance_walk endpoint root connected v.1
  cases h : distance endpoint root connected v.1 with
  | zero =>
    rw [h, Walk.zero_iff] at p
    exact (v.2 p.symm).elim
  | succ n =>
    rw [h] at p
    obtain ⟨e, b, hv, p⟩ := p.exists_last
    refine ⟨(e, !b), hv.symm, ?_⟩
    have hp := distance_le endpoint root connected p
    simpa only [Bool.not_not, h] using Nat.lt_succ_of_le hp

/-- Extraction from connectivity alone, with no supplied spanning-tree witness. -/
noncomputable def extractRootedSpanning : RootedSpanning endpoint root where
  parentEnd v := Classical.choose (exists_parentEnd endpoint root connected v)
  child_endpoint v := (Classical.choose_spec (exists_parentEnd endpoint root connected v)).1
  depth := distance endpoint root connected
  parent_depth_lt v := (Classical.choose_spec (exists_parentEnd endpoint root connected v)).2

namespace RootedSpanning

variable {endpoint root} (t : RootedSpanning endpoint root)

/-- Each non-root vertex selects the identity of its original parent edge. -/
def parentEdge (v : {v : V // v ≠ root}) : E := (t.parentEnd v).1

/-- Rank descent forbids selecting the same original edge at both ends. -/
theorem parentEdge_injective : Function.Injective t.parentEdge := by
  intro u v h
  by_cases hb : (t.parentEnd u).2 = (t.parentEnd v).2
  · apply Subtype.ext
    rw [← t.child_endpoint u, ← t.child_endpoint v]
    exact congrArg₂ endpoint h hb
  · have hb' : (t.parentEnd u).2 = !(t.parentEnd v).2 := by
      cases h₁ : (t.parentEnd u).2 <;> cases h₂ : (t.parentEnd v).2 <;> simp_all
    have hu := t.parent_depth_lt u
    have hv := t.parent_depth_lt v
    have h₁ : endpoint (t.parentEnd u).1 (!(t.parentEnd u).2) = v.1 := by
      rw [show (t.parentEnd u).1 = (t.parentEnd v).1 from h, hb', Bool.not_not]
      exact t.child_endpoint v
    have h₂ : endpoint (t.parentEnd v).1 (!(t.parentEnd v).2) = u.1 := by
      rw [← hb', ← show (t.parentEnd u).1 = (t.parentEnd v).1 from h]
      exact t.child_endpoint u
    rw [h₁] at hu
    rw [h₂] at hv
    exact (Nat.lt_asymm hu hv).elim

/-- The selected parent edges never include an original self-loop. -/
theorem parentEdge_not_loop (v : {v : V // v ≠ root}) :
    endpoint (t.parentEdge v) false ≠ endpoint (t.parentEdge v) true := by
  intro h
  have hp := t.parent_depth_lt v
  have he : endpoint (t.parentEnd v).1 (!(t.parentEnd v).2) = v.1 := by
    rw [← t.child_endpoint v]
    cases hb : (t.parentEnd v).2
    · exact h.symm
    · exact h
  rw [he] at hp
  exact Nat.lt_irrefl _ hp

/-- Original edges not used by the rooted spanning tree. -/
def Surplus := {e : E // e ∉ Set.range t.parentEdge}

noncomputable instance surplusFintype [Fintype E] : Fintype t.Surplus := by
  classical
  unfold Surplus
  infer_instance

/-- A complete, non-duplicating partition of every original edge. -/
noncomputable def edgeEquiv : ({v : V // v ≠ root} ⊕ t.Surplus) ≃ E := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective t.parentEdge t.parentEdge_injective)
    (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range t.parentEdge))

@[simp] theorem edgeEquiv_inl (v : {v : V // v ≠ root}) :
    t.edgeEquiv (.inl v) = t.parentEdge v := rfl

@[simp] theorem edgeEquiv_inr (e : t.Surplus) :
    t.edgeEquiv (.inr e) = e.1 := rfl

/-- Connectivity using only the extracted parent edges, not any surplus edge. -/
theorem selected_reachable (v : V) :
    Relation.EqvGen (Link (fun u b => endpoint (t.parentEdge u) b)) root v := by
  let R := Relation.EqvGen (Link (fun u b => endpoint (t.parentEdge u) b))
  have step (u : {v : V // v ≠ root}) :
      R (endpoint (t.parentEnd u).1 (!(t.parentEnd u).2)) u.1 := by
    rw [← t.child_endpoint u]
    cases h : (t.parentEnd u).2 with
    | false => exact .symm _ _ (.rel _ _ ⟨u, rfl, rfl⟩)
    | true => exact .rel _ _ ⟨u, rfl, rfl⟩
  have go : ∀ n v, t.depth v = n → R root v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn
      by_cases hv : v = root
      · subst v; exact .refl _
      · let u : {v : V // v ≠ root} := ⟨v, hv⟩
        have hp := t.parent_depth_lt u
        have hlt : t.depth (endpoint (t.parentEnd u).1 (!(t.parentEnd u).2)) < n := by
          simpa only [u, hn] using hp
        exact .trans _ _ _ (ih _ hlt _ rfl) (step u)
  exact go _ v rfl

open scoped Classical in
/-- Exact Euler count of the extracted partition, valid for arbitrary multigraphs. -/
theorem edge_card_add_one [Fintype V] [Fintype E] :
    Fintype.card E + 1 = Fintype.card V + Fintype.card t.Surplus := by
  classical
  have he := Fintype.card_congr t.edgeEquiv
  rw [Fintype.card_sum] at he
  have hv : Fintype.card {v : V // v ≠ root} = Fintype.card V - 1 := by
    simp [Fintype.card_subtype_compl]
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  omega

include t in
open scoped Classical in
/-- Connectivity forces at least one fewer original edges than vertices. -/
theorem vertices_le_edges_add_one [Fintype V] [Fintype E] :
    Fintype.card V ≤ Fintype.card E + 1 := by
  have h := t.edge_card_add_one
  omega

open scoped Classical in
/-- Every connected component surviving the density test has at most one
original edge outside the extracted rooted spanning tree. -/
theorem surplus_card_le_one [Fintype V] [Fintype E]
    (sparse : Fintype.card E ≤ Fintype.card V) : Fintype.card t.Surplus ≤ 1 := by
  have h := t.edge_card_add_one
  omega

open scoped Classical in
/-- The tree-count case has no extra edge at all. -/
theorem surplus_card_eq_zero [Fintype V] [Fintype E]
    (tree : Fintype.card E + 1 = Fintype.card V) : Fintype.card t.Surplus = 0 := by
  have h := t.edge_card_add_one
  omega

open scoped Classical in
/-- The unicyclic-count case has exactly one original surplus edge. -/
theorem surplus_card_eq_one [Fintype V] [Fintype E]
    (unicycle : Fintype.card E = Fintype.card V) : Fintype.card t.Surplus = 1 := by
  have h := t.edge_card_add_one
  omega

end RootedSpanning

end Holant.OneHot.Decomposition
