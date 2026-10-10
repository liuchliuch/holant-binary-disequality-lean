import Holant.Complexity.FixedGadgetSubstitution.Raw

/-! Every literal replacement record passes the existing closed-network
validator. The proof tracks endpoint multiplicities, including loops and
parallel edges, rather than merely their support. -/
namespace Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork

 theorem edgeEnds_add (offset a b : ℕ) :
    edgeEnds offset (a+b) = edgeEnds offset a ++ edgeEnds (offset+a) b := by
  simp [edgeEnds, List.range_add, List.flatMap_append, List.flatMap_map,
    Function.comp_def, Nat.add_assoc]

 theorem edgeEnds_shift (offset count : ℕ) :
    (edgeEnds 0 count).map (fun p => (offset+p.1,p.2)) = edgeEnds offset count := by
  simp [edgeEnds, List.map_flatMap, Function.comp_def]

 theorem map_range_getD {α : Type} (xs : List α) (default : α) :
    (List.range xs.length).map (fun i => xs.getD i default) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [List.range_succ_eq_map, List.map_map, Function.comp_def] using congrArg (x :: ·) ih

 theorem expectedEndpoints_eq (r : RawClosedNetwork) :
    r.expectedEndpoints = edgeEnds 0 r.edges.length := by
  unfold RawClosedNetwork.expectedEndpoints edgeEnds
  simp only [List.flatMap, Nat.zero_add]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

namespace Template

 theorem place_expectedEndpoints (g : Template) (offset : ℕ)
    (boundary : List RawEndpoint) (hb : boundary.length = g.boundary) :
    g.expectedEndpoints.map (placeEndpoint offset boundary) =
      boundary ++ edgeEnds offset g.edges.length := by
  simp only [expectedEndpoints, List.map_append, List.map_map]
  change (List.range g.boundary).map (fun i => boundary.getD i (0,false)) ++
    (edgeEnds 0 g.edges.length).map (fun p => (offset+p.1,p.2)) = _
  rw [← hb, map_range_getD, edgeEnds_shift]

 theorem place_endpoints_perm {s b : ℕ} {arity : ℕ → ℕ}
    (g : Template) (hg : g.WellFormed s b arity) (offset : ℕ)
    (boundary : List RawEndpoint) (hb : boundary.length = g.boundary) :
    ((g.placeVertices offset boundary).map Prod.snd).flatten.Perm
      (boundary ++ edgeEnds offset g.edges.length) := by
  rw [placeVertices_endpoints, ← g.place_expectedEndpoints offset boundary hb]
  exact hg.2.2.map _

 theorem place_vertices_valid {s b : ℕ} {arity : ℕ → ℕ}
    (g : Template) (hg : g.WellFormed s b arity) (offset : ℕ)
    (boundary : List RawEndpoint) :
    ∀ row ∈ g.placeVertices offset boundary,
      row.1 < s ∧ row.2.length = arity row.1 := by
  intro row hr
  obtain ⟨vertex, hl, rfl⟩ := List.mem_map.mp hr
  simpa using hg.1 vertex hl

end Template

/-- All internal ends allocated by expansion form one consecutive fresh block. -/
 theorem expandRows_endpoints_perm (templates : ℕ → Template) (offset : ℕ)
    (rows : List RawVertex) (s b : ℕ) (arity : ℕ → ℕ)
    (h : ∀ row ∈ rows, (templates row.1).WellFormed s b arity ∧
      row.2.length = (templates row.1).boundary) :
    (expandRows templates offset rows).endpoints.Perm
      ((rows.map Prod.snd).flatten ++
        edgeEnds offset (expandRows templates offset rows).edges.length) := by
  induction rows generalizing offset with
  | nil => simp [expandRows, RawClosedNetwork.endpoints]
  | cons row rows ih =>
    have hg := h row (by simp)
    have ht := ih (offset+(templates row.1).edges.length) (by
      intro x hx; exact h x (by simp [hx]))
    have hh := (templates row.1).place_endpoints_perm hg.1 offset row.2 hg.2
    simp only [expandRows, RawClosedNetwork.endpoints, List.map_append,
      List.flatten_append] at *
    have hp := hh.append ht
    simp only [List.length_append, List.map_cons, List.flatten_cons, edgeEnds_add]
    exact hp.trans (by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := edgeEnds offset (templates row.1).edges.length)
          (l₂ := (rows.map Prod.snd).flatten)).append_left row.2 |>.append_right
            (edgeEnds (offset+(templates row.1).edges.length)
              (expandRows templates (offset+(templates row.1).edges.length) rows).edges.length))

 theorem expandRows_vertices_valid (templates : ℕ → Template) (offset : ℕ)
    (rows : List RawVertex) (s b : ℕ) (arity : ℕ → ℕ)
    (h : ∀ row ∈ rows, (templates row.1).WellFormed s b arity) :
    ∀ row ∈ (expandRows templates offset rows).vertices,
      row.1 < s ∧ row.2.length = arity row.1 := by
  induction rows generalizing offset with
  | nil => simp [expandRows]
  | cons row rows ih =>
    intro out hout
    rcases List.mem_append.mp hout with hg | ht
    · exact (templates row.1).place_vertices_valid (h row (by simp)) offset row.2 out hg
    · exact ih _ (by intro x hx; exact h x (by simp [hx])) out ht

 theorem expandRows_edges_valid (templates : ℕ → Template) (offset : ℕ)
    (rows : List RawVertex) (s b : ℕ) (arity : ℕ → ℕ)
    (h : ∀ row ∈ rows, (templates row.1).WellFormed s b arity) :
    ∀ label ∈ (expandRows templates offset rows).edges, label < b := by
  rw [expandRows_edges]
  intro label hl
  obtain ⟨labels, hs, hl⟩ := List.mem_flatten.mp hl
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hs
  exact (h row hr).2.1 label hl

/-- The complete generated graph satisfies the existing faithful validator. -/
 theorem replace_wellFormed (templates : ℕ → Template) (r : RawClosedNetwork)
    {sourceCount s b : ℕ} {sourceArity arity : ℕ → ℕ}
    (hr : r.WellFormed sourceCount b sourceArity)
    (hg : ∀ label < sourceCount, (templates label).WellFormed s b arity ∧
      (templates label).boundary = sourceArity label) :
    (replace templates r).WellFormed s b arity := by
  have hv : ∀ row ∈ r.vertices, (templates row.1).WellFormed s b arity ∧
      row.2.length = (templates row.1).boundary := by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hrow
    exact ⟨(hg _ (hr.1 i).1).1, (hr.1 i).2.trans (hg _ (hr.1 i).1).2.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact expandRows_vertices_valid templates r.edges.length r.vertices s b arity
      (fun row hrow => (hv row hrow).1) _ (List.get_mem _ v)
  · intro e
    have he : (replace templates r).edges.get e ∈ r.edges ++
        (expandRows templates r.edges.length r.vertices).edges := List.get_mem _ e
    rcases List.mem_append.mp he with old | new
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp old
      rw [← hi]
      exact hr.2.1 i
    · exact expandRows_edges_valid templates r.edges.length r.vertices s b arity
        (fun row hrow => (hv row hrow).1) _ new
  · have hp := expandRows_endpoints_perm templates r.edges.length r.vertices s b arity hv
    have hq := hr.2.2.append_right
      (edgeEnds r.edges.length (expandRows templates r.edges.length r.vertices).edges.length)
    rw [expectedEndpoints_eq] at hq
    rw [expectedEndpoints_eq]
    change (expandRows templates r.edges.length r.vertices).endpoints.Perm _
    have hfinal := hp.trans hq
    simpa only [replace, List.length_append, edgeEnds_add, Nat.zero_add] using hfinal

end Holant.Complexity.FixedGadgetSubstitution
