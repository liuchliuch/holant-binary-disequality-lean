import Holant.OneHot.Computable.Components
import Holant.OneHot.Decomposition.Extraction

/-!
# Actual framed input to computed components and original semantic incidence

The executable graph table is obtained from validated stored port occurrences.
Counts are bounded by actual framed input length. Edge IDs, orientations and local
port indexes are retained, and the component labels agree exactly with the
semantic quotient. This file does not assert a bit-time machine implementation.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.Complexity.RawClosedNetwork

open Holant.OneHot.Computable Holant.OneHot.Decomposition

variable {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)

/-- Every table row comes from the two original stored port occurrences. -/
def graph (h : r.WellFormed s b arity) : Graph where
  vertices := r.vertices.length
  edges := List.ofFn fun e : Fin r.edges.length =>
    ((r.lookup h (e, false)).1, (r.lookup h (e, true)).1)

@[simp] theorem graph_vertices (h : r.WellFormed s b arity) :
    (r.graph h).vertices = r.vertices.length := rfl

@[simp] theorem graph_edges (h : r.WellFormed s b arity) :
    (r.graph h).edges.length = r.edges.length := by simp [graph]

/-- Only the proof of the index bound changes; the original numerical ID does not. -/
def graphEdgeEquiv (h : r.WellFormed s b arity) : (r.graph h).Edge ≃ Fin r.edges.length :=
  finCongr (r.graph_edges h)

@[simp] theorem graphEdgeEquiv_val (h : r.WellFormed s b arity) (e : (r.graph h).Edge) :
    (r.graphEdgeEquiv h e).val = e.val := rfl

@[simp] theorem graph_endpoint (h : r.WellFormed s b arity) (e : (r.graph h).Edge) (z : Bool) :
    (r.graph h).endpoint e z = (r.shape h).endpoint (r.graphEdgeEquiv h e) z := by
  cases z <;> simp [Graph.endpoint, graph, graphEdgeEquiv, lookup_vertex]
  all_goals congr 1

theorem graph_link (h : r.WellFormed s b arity) :
    Link (r.graph h).endpoint = (r.shape h).EdgeLink := by
  funext u v
  apply propext
  constructor
  · rintro ⟨e, hu, hv⟩
    exact ⟨r.graphEdgeEquiv h e, by simpa using hu, by simpa using hv⟩
  · rintro ⟨e, hu, hv⟩
    exact ⟨(r.graphEdgeEquiv h).symm e, by simpa using hu, by simpa using hv⟩

/-- The executed `V`-round table computes the actual decoded graph's connectivity. -/
theorem graph_reach_iff (h : r.WellFormed s b arity) (u v : Fin r.vertices.length) :
    v ∈ (r.graph h).reach u r.vertices.length ↔ (r.shape h).Reachable u v := by
  exact ((r.graph h).reach_iff u v).trans (by rw [r.graph_link h])

/-- Computed component IDs are exactly the old quotient's equality classes. -/
theorem graph_label_eq_iff (h : r.WellFormed s b arity) (u v : Fin r.vertices.length) :
    (r.graph h).label u = (r.graph h).label v ↔
      (r.shape h).componentOf u = (r.shape h).componentOf v := by
  rw [(r.graph h).label_eq_iff, r.graph_link h, (r.shape h).componentOf_eq_iff]

/-- No compressed integer field controls a graph-size loop. The loop bounds
are the explicit record counts, bounded by the actual framed byte string. -/
theorem graph_counts_le_bits (h : r.WellFormed s b arity) :
    (r.graph h).vertices + (r.graph h).edges.length ≤ (encoding.encode r).length := by
  rw [r.graph_edges h]
  exact r.counts_le_encoded_length

/-- The measured original-end tests for a single component search are bounded
by a cubic polynomial in actual serialized input length. This counter does not
include comparison bit costs, allocation, parsing, or a finite-machine simulation. -/
theorem graph_reach_tests_le_bits (h : r.WellFormed s b arity) (root : Fin r.vertices.length) :
    ((r.graph h).reachRun root r.vertices.length).2 ≤ 2 * (encoding.encode r).length ^ 3 := by
  have hc := (r.graph h).reach_work_le root r.vertices.length
  have hn := r.counts_le_encoded_length
  have hv : r.vertices.length ≤ (encoding.encode r).length := by omega
  have he : r.edges.length ≤ (encoding.encode r).length := by omega
  rw [r.graph_edges h] at hc
  change ((r.graph h).reachRun root r.vertices.length).2 ≤
    r.vertices.length * (2 * r.vertices.length * r.edges.length) at hc
  calc
    _ ≤ r.vertices.length * (2 * r.vertices.length * r.edges.length) := hc
    _ ≤ (encoding.encode r).length * (2 * (encoding.encode r).length * (encoding.encode r).length) :=
      Nat.mul_le_mul hv (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hv) he)
    _ = _ := by simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]

end Holant.Complexity.RawClosedNetwork
