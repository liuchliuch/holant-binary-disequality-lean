import Holant.Complexity.EdgeSubdivision.WireEquivalence

/-! Linear graph-size bounds for both directions of the actual substitution,
separate from its already proved polynomial encoded-machine cost. -/
namespace Holant.Complexity.EdgeSubdivision.WireEquivalence
open FixedGadgetSubstitution

theorem template_vertices_le (s : ℕ) (arity : ℕ → ℕ) (i : ℕ) :
    (WireMacros.templates s arity i).vertices.length ≤ 2 := by
  unfold WireMacros.templates
  split_ifs <;>
    simp [identityTemplate,WirePath.template,Labelling.template,WirePath.labelling,WirePath.shape]

theorem template_edges_le (s : ℕ) (arity : ℕ → ℕ) (i : ℕ) :
    (WireMacros.templates s arity i).edges.length ≤ 1 := by
  unfold WireMacros.templates
  split_ifs <;>
    simp [identityTemplate,WirePath.template,Labelling.template,WirePath.labelling,WirePath.shape]

theorem expanded_vertices_le (s : ℕ) (arity : ℕ → ℕ)
    (offset : ℕ) (rows : List RawVertex) :
    (expandRows (WireMacros.templates s arity) offset rows).vertices.length ≤ 2*rows.length := by
  induction rows generalizing offset with
  | nil => simp [expandRows]
  | cons row rows ih =>
    simp only [expandRows,List.length_append,Template.placeVertices_length,List.length_cons]
    have ht := template_vertices_le s arity row.1
    have hh := ih (offset+(WireMacros.templates s arity row.1).edges.length)
    omega

theorem expanded_edges_le (s : ℕ) (arity : ℕ → ℕ)
    (offset : ℕ) (rows : List RawVertex) :
    (expandRows (WireMacros.templates s arity) offset rows).edges.length ≤ rows.length := by
  induction rows generalizing offset with
  | nil => simp [expandRows]
  | cons row rows ih =>
    simp only [expandRows,List.length_append,List.length_cons]
    have ht := template_edges_le s arity row.1
    have hh := ih (offset+(WireMacros.templates s arity row.1).edges.length)
    omega

theorem query_vertices_le (s : ℕ) (arity : ℕ → ℕ) (r : Input s arity) :
    (query s arity r).val.vertices.length ≤ 2*(r.val.vertices.length+r.val.edges.length) := by
  change (expandRows (WireMacros.templates s arity) (subdivide (s+1) r.val).edges.length
    (subdivide (s+1) r.val).vertices).vertices.length ≤ _
  simpa only [vertices_length] using expanded_vertices_le s arity
    (subdivide (s+1) r.val).edges.length (subdivide (s+1) r.val).vertices

theorem query_edges_le (s : ℕ) (arity : ℕ → ℕ) (r : Input s arity) :
    (query s arity r).val.edges.length ≤ r.val.vertices.length+3*r.val.edges.length := by
  change ((subdivide (s+1) r.val).edges ++
    (expandRows (WireMacros.templates s arity) (subdivide (s+1) r.val).edges.length
      (subdivide (s+1) r.val).vertices).edges).length ≤ _
  rw [List.length_append,edges_length]
  have h := expanded_edges_le s arity (subdivide (s+1) r.val).edges.length
    (subdivide (s+1) r.val).vertices
  rw [vertices_length,edges_length] at h
  omega

theorem query_size_le (s : ℕ) (arity : ℕ → ℕ) (r : Input s arity) :
    (query s arity r).val.vertices.length+(query s arity r).val.edges.length ≤
      5*(r.val.vertices.length+r.val.edges.length) := by
  have hv := query_vertices_le s arity r
  have he := query_edges_le s arity r
  omega

end Holant.Complexity.EdgeSubdivision.WireEquivalence
