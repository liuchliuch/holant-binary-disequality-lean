import Holant.OneHot.Computable.Rooted

/-!
# Executable component representatives

Every vertex is labelled by the least original vertex in its computed reachable
set. The component list scans the original vertex range; it never enumerates a
quotient or the power set of vertices. Equal labels are proved equivalent to
actual original-edge connectivity. Empty graphs have an empty component list.
-/

namespace Holant.OneHot.Computable.Graph

open Holant.OneHot.Decomposition

variable (g : Graph)

def label (v : g.Vertex) : g.Vertex :=
  (g.reach v g.vertices).min' ⟨v, g.root_mem_reach v _⟩

theorem label_mem (v : g.Vertex) : g.label v ∈ g.reach v g.vertices :=
  Finset.min'_mem _ _

theorem label_reachable (v : g.Vertex) : Relation.EqvGen (Link g.endpoint) v (g.label v) :=
  (g.reach_iff _ _).mp (g.label_mem v)

theorem reach_eq_of_reachable {u v : g.Vertex}
    (h : Relation.EqvGen (Link g.endpoint) u v) :
    g.reach u g.vertices = g.reach v g.vertices := by
  ext w
  rw [g.reach_iff, g.reach_iff]
  exact ⟨fun hw => .trans _ _ _ (.symm _ _ h) hw, fun hw => .trans _ _ _ h hw⟩

theorem label_eq_of_reachable {u v : g.Vertex}
    (h : Relation.EqvGen (Link g.endpoint) u v) : g.label u = g.label v := by
  unfold label
  congr 1
  exact g.reach_eq_of_reachable h

/-- The computed integer labels identify exactly the semantic components. -/
theorem label_eq_iff (u v : g.Vertex) :
    g.label u = g.label v ↔ Relation.EqvGen (Link g.endpoint) u v := by
  constructor
  · intro h
    have hu := g.label_reachable u
    rw [h] at hu
    exact .trans _ _ _ hu (.symm _ _ (g.label_reachable v))
  · exact g.label_eq_of_reachable

@[simp] theorem label_idempotent (v : g.Vertex) : g.label (g.label v) = g.label v :=
  g.label_eq_of_reachable (.symm _ _ (g.label_reachable v))

/-- Concrete original-vertex IDs, in increasing order. -/
def roots (g : Graph) : List g.Vertex :=
  (List.finRange g.vertices).filter fun v => decide (g.label v = v)

@[simp] theorem mem_roots (v : g.Vertex) : v ∈ g.roots ↔ g.label v = v := by
  simp [roots]

@[simp] theorem label_mem_roots (v : g.Vertex) : g.label v ∈ g.roots := by simp

theorem roots_nodup : g.roots.Nodup := List.Nodup.filter _ (List.nodup_finRange _)

theorem roots_length_le : g.roots.length ≤ g.vertices := by
  simpa [roots] using List.length_filter_le (fun v : g.Vertex => decide (g.label v = v))
    (List.finRange g.vertices)

/-- No representative is manufactured for the empty graph. -/
theorem roots_empty_of_no_vertices (h : g.vertices = 0) : g.roots = [] := by
  apply List.eq_nil_of_length_eq_zero
  have hb := g.roots_length_le
  omega

theorem endpoint_labels (e : g.Edge) (z : Bool) :
    g.label (g.endpoint e z) = g.label (g.endpoint e false) := by
  cases z
  · rfl
  · exact g.label_eq_of_reachable (.symm _ _ (.rel _ _ ⟨e, rfl, rfl⟩))

/-- Filtering IDs keeps every vertex once across the computed component lists. -/
def componentVertices (root : g.Vertex) : List g.Vertex :=
  (List.finRange g.vertices).filter fun v => decide (g.label v = root)

/-- Filtering edge IDs retains all parallel edges and self-loops individually. -/
def componentEdges (root : g.Vertex) : List g.Edge :=
  (List.finRange g.edges.length).filter fun e => decide (g.label (g.endpoint e false) = root)

@[simp] theorem mem_componentVertices (root v : g.Vertex) :
    v ∈ g.componentVertices root ↔ g.label v = root := by simp [componentVertices]

@[simp] theorem mem_componentEdges (root : g.Vertex) (e : g.Edge) :
    e ∈ g.componentEdges root ↔ g.label (g.endpoint e false) = root := by simp [componentEdges]

theorem componentVertices_iff_fiber (root v : g.Vertex) (hr : root ∈ g.roots) :
    v ∈ g.componentVertices root ↔ v ∈ g.reach root g.vertices := by
  rw [mem_componentVertices, g.reach_iff]
  have hr' := (g.mem_roots root).mp hr
  constructor
  · intro h
    exact .symm _ _ ((g.label_eq_iff v root).mp (h.trans hr'.symm))
  · intro h
    exact ((g.label_eq_iff v root).mpr (.symm _ _ h)).trans hr'

/-- Every original vertex occurs in exactly one computed component, including
isolated vertices. The uniqueness is about actual returned root IDs. -/
theorem unique_vertex_component (v : g.Vertex) :
    ∃! root : g.Vertex, root ∈ g.roots ∧ v ∈ g.componentVertices root := by
  refine ⟨g.label v, ⟨g.label_mem_roots v, by simp⟩, ?_⟩
  intro root h
  exact ((g.mem_componentVertices root v).mp h.2).symm

/-- Every original edge occurs in exactly one computed component. Original edge
IDs keep multiplicity, so this also covers parallel edges and self-loops. -/
theorem unique_edge_component (e : g.Edge) :
    ∃! root : g.Vertex, root ∈ g.roots ∧ e ∈ g.componentEdges root := by
  refine ⟨g.label (g.endpoint e false), ⟨g.label_mem_roots _, by simp⟩, ?_⟩
  intro root h
  exact ((g.mem_componentEdges root e).mp h.2).symm

end Holant.OneHot.Computable.Graph
