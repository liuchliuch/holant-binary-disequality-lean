import Holant.Complexity.ClosedNetworkSemantics
import Mathlib.Data.List.Range

/-!
# Literal fixed-gadget replacement records

A template contains ordered original-family vertices and an explicit partition of
its port occurrences into boundary positions and internal edge ends. Replacement
copies those records and offsets only internal edge IDs. The external endpoints
are read from the original vertex row in their original order. No incidence map,
connectivity certificate, or already-replaced graph is part of the input.
-/
namespace Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork

abbrev LocalEndpoint := ℕ ⊕ RawEndpoint
abbrev LocalVertex := ℕ × List LocalEndpoint

/-- Consecutive, oriented edge ends. Both occurrences of a loop remain distinct. -/
def edgeEnds (offset count : ℕ) : List RawEndpoint :=
  (List.range count).flatMap fun e => [(offset + e, false), (offset + e, true)]

@[simp] theorem edgeEnds_zero (offset : ℕ) : edgeEnds offset 0 = [] := rfl

@[simp] theorem edgeEnds_length (offset count : ℕ) :
    (edgeEnds offset count).length = 2 * count := by
  simp [edgeEnds, List.length_flatMap, Nat.mul_comm]

/-- A literal ordered open network with ordinary boundary ports. -/
structure Template where
  boundary : ℕ
  vertices : List LocalVertex
  edges : List ℕ
  deriving DecidableEq

namespace Template

def endpoints (g : Template) : List LocalEndpoint := (g.vertices.map Prod.snd).flatten

def expectedEndpoints (g : Template) : List LocalEndpoint :=
  (List.range g.boundary).map Sum.inl ++ (edgeEnds 0 g.edges.length).map Sum.inr

/-- A finite template retains all original-family labels, including nullary
vertices; every boundary and internal edge-end occurrence appears exactly once. -/
def WellFormed (s b : ℕ) (arity : ℕ → ℕ) (g : Template) : Prop :=
  (∀ row ∈ g.vertices, row.1 < s ∧ row.2.length = arity row.1) ∧
  (∀ label ∈ g.edges, label < b) ∧ g.endpoints.Perm g.expectedEndpoints

instance (s b : ℕ) (arity : ℕ → ℕ) (g : Template) :
    Decidable (g.WellFormed s b arity) := by unfold WellFormed; infer_instance

/-- Boundary slots refer to the incoming row, while local edge IDs receive a
fresh offset. The default is consulted only on malformed boundary rows. -/
def placeEndpoint (offset : ℕ) (boundary : List RawEndpoint) : LocalEndpoint → RawEndpoint
  | .inl i => boundary.getD i (0, false)
  | .inr p => (offset + p.1, p.2)

def placeVertices (g : Template) (offset : ℕ) (boundary : List RawEndpoint) : List RawVertex :=
  g.vertices.map fun row => (row.1, row.2.map (placeEndpoint offset boundary))

@[simp] theorem placeVertices_length (g : Template) (offset : ℕ) (boundary : List RawEndpoint) :
    (g.placeVertices offset boundary).length = g.vertices.length := by simp [placeVertices]

@[simp] theorem placeVertices_endpoints (g : Template) (offset : ℕ) (boundary : List RawEndpoint) :
    ((g.placeVertices offset boundary).map Prod.snd).flatten =
      g.endpoints.map (placeEndpoint offset boundary) := by
  simp [placeVertices, endpoints, List.map_flatten, List.map_map, Function.comp_def]

end Template

/-- Expand rows in their literal input order. Internal edge blocks are allocated
consecutively after all original edges. This is an executable recursive compiler
specification; the separate bit-machine proof must implement this function. -/
def expandRows (templates : ℕ → Template) (offset : ℕ) : List RawVertex → RawClosedNetwork
  | [] => ⟨[], []⟩
  | row :: rows =>
    let g := templates row.1
    let tail := expandRows templates (offset + g.edges.length) rows
    ⟨g.placeVertices offset row.2 ++ tail.vertices, g.edges ++ tail.edges⟩

/-- The query graph keeps the original edge labels and appends the fresh internal
blocks. Original external IDs and orientations are never renumbered. -/
def replace (templates : ℕ → Template) (r : RawClosedNetwork) : RawClosedNetwork :=
  let expanded := expandRows templates r.edges.length r.vertices
  ⟨expanded.vertices, r.edges ++ expanded.edges⟩

@[simp] theorem expandRows_nil (templates : ℕ → Template) (offset : ℕ) :
    expandRows templates offset [] = ⟨[], []⟩ := rfl

@[simp] theorem expandRows_vertex_count (templates : ℕ → Template) (offset : ℕ)
    (rows : List RawVertex) :
    (expandRows templates offset rows).vertices.length =
      (rows.map fun row => (templates row.1).vertices.length).sum := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih => simp [expandRows, ih]

@[simp] theorem expandRows_edges (templates : ℕ → Template) (offset : ℕ)
    (rows : List RawVertex) :
    (expandRows templates offset rows).edges =
      (rows.map fun row => (templates row.1).edges).flatten := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih => simp [expandRows, ih]

@[simp] theorem replace_vertex_count (templates : ℕ → Template) (r : RawClosedNetwork) :
    (replace templates r).vertices.length =
      (r.vertices.map fun row => (templates row.1).vertices.length).sum := by
  simp [replace]

@[simp] theorem replace_edge_count (templates : ℕ → Template) (r : RawClosedNetwork) :
    (replace templates r).edges.length = r.edges.length +
      (r.vertices.map fun row => (templates row.1).edges.length).sum := by
  simp [replace, List.length_flatten, List.map_map, Function.comp_def]

/-- Number of replaced occurrences comes from the actual original label stream. -/
def occurrences (label : ℕ) (r : RawClosedNetwork) : ℕ :=
  (r.vertices.filter fun row => row.1 == label).length

theorem occurrences_le_input_length (label : ℕ) (r : RawClosedNetwork) :
    occurrences label r ≤ (RawClosedNetwork.encoding.encode r).length := by
  have h := List.length_filter_le (fun row : RawVertex => row.1 == label) r.vertices
  have hh := r.counts_le_encoded_length
  unfold occurrences
  omega

end Holant.Complexity.FixedGadgetSubstitution
