import Holant.Complexity.BinaryInterpolation.Chains.Compiler.RawCorrectness

/-! The temporary B-label counter is exactly (k+1)m. Endpoint placement and
fresh edge offsets do not affect the actual original/generated label stream.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
open FixedGadgetSubstitution RawClosedNetwork
set_option backward.isDefEq.respectTransparency false

theorem place_label_count (g : Template) (offset : ℕ) (boundary : List RawEndpoint) (label : ℕ) :
    ((g.placeVertices offset boundary).filter (fun row => row.1 == label)).length =
      (g.vertices.filter (fun row => row.1 == label)).length := by
  unfold Template.placeVertices
  generalize g.vertices = rs
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : r.1 = label <;> simp [h,ih]

theorem expandRows_label_count (ts : ℕ → Template) (offset : ℕ) (rs : List RawVertex) (label : ℕ) :
    ((expandRows ts offset rs).vertices.filter (fun row => row.1 == label)).length =
      (rs.map (fun row => ((ts row.1).vertices.filter (fun q => q.1 == label)).length)).sum := by
  induction rs generalizing offset with
  | nil => rfl
  | cons r rs ih =>
    simp [expandRows,List.filter_append,place_label_count,ih]

theorem template_label_count (arity : ℕ → ℕ) (label edge k i : ℕ) :
    ((templates arity label label edge k i).vertices.filter (fun row => row.1 == label)).length =
      if i = label then k + 1 else 0 := by
  by_cases h : i = label
  · subst i
    simp [templates,explicitTemplate,explicitRow,List.filter_map,Function.comp_def]
  · simp [templates,h,identityTemplate]

/-- The source slot denotes H and the same intermediate slot denotes B. Its
counter is derived from the actual emitted rows, not a supplied certificate. -/
theorem raw_label_count (s b : ℕ) (arity : ℕ → ℕ) (label edge : ℕ) (x : Input s b arity) :
    occurrences label (raw s b arity label label edge x) =
      (x.1 + 1) * occurrences label x.2.val := by
  rw [raw_eq_replace]
  change ((expandRows (templates arity label label edge x.1) x.2.val.edges.length
    x.2.val.vertices).vertices.filter (fun row => row.1 == label)).length = _
  rw [expandRows_label_count]
  simp only [template_label_count]
  have h := prefix_edges arity label label edge (x.1 + 1) x.2.val.vertices
  simpa only [template_edges,FixedGadgetSubstitution.Compiler.indicator_sum,
    FixedGadgetSubstitution.occurrences] using h

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
