import Holant.Complexity.UniversalPairReduction.Smoothing

/-! The literal edge table and endpoint bounds needed to identify the smoothing
machine's emitted zero labels with deletion from the original edge stream. -/
namespace Holant.Complexity.RawClosedNetwork

variable {s b : ℕ} {arity : ℕ → ℕ} {r : RawClosedNetwork}

/-- Every endpoint in a validated raw record refers to an actual edge row. -/
theorem endpoint_mem_bound (h : r.WellFormed s b arity) {p : RawEndpoint}
    (hp : p ∈ r.endpoints) : p.1 < r.edges.length :=
  (r.mem_expectedEndpoints_iff p).mp (h.2.2.mem_iff.mp hp)

/-- A port in any original vertex row is an endpoint of the full raw record. -/
theorem row_endpoint_mem {row : RawVertex} (hr : row ∈ r.vertices)
    {p : RawEndpoint} (hp : p ∈ row.2) : p ∈ r.endpoints := by
  apply List.mem_flatten.mpr
  exact ⟨row.2, List.mem_map.mpr ⟨row, hr, rfl⟩, hp⟩

/-- A single allowed edge label forces every literal edge entry to be zero. -/
theorem edges_eq_replicate (h : r.WellFormed s 1 arity) :
    r.edges = List.replicate r.edges.length 0 := by
  apply List.eq_replicate_of_mem
  intro label hlabel
  obtain ⟨e, he⟩ := List.mem_iff_get.mp hlabel
  have hb := h.2.1 e
  rw [he] at hb
  omega

/-- Deleting an actual edge row leaves exactly one fewer zero-labelled row. -/
theorem edges_eraseIdx_eq_replicate (h : r.WellFormed s 1 arity)
    {e : ℕ} (he : e < r.edges.length) :
    r.edges.eraseIdx e = List.replicate (r.edges.length - 1) 0 := by
  have hz := r.edges_eq_replicate h
  calc
    r.edges.eraseIdx e = (List.replicate r.edges.length 0).eraseIdx e :=
      congrArg (fun edges : List ℕ => edges.eraseIdx e) hz
    _ = List.replicate (r.edges.length - 1) 0 := by
      simp [List.eraseIdx_replicate, he]

end Holant.Complexity.RawClosedNetwork

namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler

variable (s : ℕ) (arity : ℕ → ℕ)

theorem input_edges_eq_replicate (r : Input s arity) :
    r.val.edges = List.replicate r.val.edges.length 0 :=
  r.val.edges_eq_replicate r.property.1

/-- Both ordered ports of the actual row found by the label search have valid
edge IDs, whether they belong to one self-loop or two different edges. -/
theorem found_endpoints_bound (r : Input s arity) (row : RawVertex)
    (h : r.val.vertices[r.val.vertices.findIdx (fun row => row.1 == s)]? = some row)
    (first second : RawEndpoint) (hrow : row.2 = [first, second]) :
    first.1 < r.val.edges.length ∧ second.1 < r.val.edges.length := by
  have hr : row ∈ r.val.vertices := List.mem_of_getElem? h
  constructor
  · exact r.val.endpoint_mem_bound r.property.1
      (r.val.row_endpoint_mem hr (by simp [hrow]))
  · exact r.val.endpoint_mem_bound r.property.1
      (r.val.row_endpoint_mem hr (by simp [hrow]))

theorem input_edges_eraseIdx_eq_replicate (r : Input s arity) {e : ℕ}
    (he : e < r.val.edges.length) :
    r.val.edges.eraseIdx e = List.replicate (r.val.edges.length - 1) 0 :=
  r.val.edges_eraseIdx_eq_replicate r.property.1 he

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
