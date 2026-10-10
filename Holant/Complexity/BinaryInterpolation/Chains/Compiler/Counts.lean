import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Validated

/-! Exact occurrence counts and the source's quadratic per-query and cubic
aggregate added-vertex bounds. Counts are taken in the original input graph.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
open FixedGadgetSubstitution RawClosedNetwork
set_option backward.isDefEq.respectTransparency false

@[simp] theorem template_vertices (arity : ℕ → ℕ) (distinguished label edge k i : ℕ) :
    (templates arity distinguished label edge k i).vertices.length =
      if i = distinguished then k + 1 else 1 := by
  by_cases h : i = distinguished <;> simp [templates,h,identityTemplate]

theorem vertex_sum (arity : ℕ → ℕ) (distinguished label edge k : ℕ) (rs : List RawVertex) :
    (rs.map (fun row => (templates arity distinguished label edge k row.1).vertices.length)).sum =
      rs.length + k * (rs.filter (fun row => row.1 == distinguished)).length := by
  induction rs with
  | nil => simp
  | cons row rs ih =>
    simp only [List.map_cons,List.sum_cons,template_vertices] at ih ⊢
    by_cases h : row.1 = distinguished <;>
      simp [h,ih,Nat.mul_add] <;> omega

theorem raw_vertices (s b : ℕ) (arity : ℕ → ℕ) (distinguished label edge : ℕ)
    (x : Input s b arity) :
    (raw s b arity distinguished label edge x).vertices.length =
      x.2.val.vertices.length + x.1 * occurrences distinguished x.2.val := by
  rw [raw_eq_replace,replace_vertex_count,vertex_sum]
  rfl

theorem raw_edges (s b : ℕ) (arity : ℕ → ℕ) (distinguished label edge : ℕ)
    (x : Input s b arity) :
    (raw s b arity distinguished label edge x).edges.length =
      x.2.val.edges.length + x.1 * occurrences distinguished x.2.val := by
  rw [raw_eq_replace,replace_edge_count,prefix_edges,FixedGadgetSubstitution.Compiler.indicator_sum]
  rfl

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence

namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.Validated
open FixedGadgetSubstitution RawClosedNetwork
open scoped BigOperators
variable {s b : ℕ} (arity : ℕ → ℕ)
variable (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)

theorem bounded_vertices (x : BoundedQueries.Input (s + 1) b (extendedArity s arity) s) :
    (boundedValue arity label hlabel edge x).val.vertices.length =
      x.1.val.vertices.length + x.2.val * occurrences s x.1.val :=
  Occurrence.raw_vertices (s + 1) b (extendedArity s arity) s label.val edge.val (x.2.val,x.1)

theorem bounded_edges (x : BoundedQueries.Input (s + 1) b (extendedArity s arity) s) :
    (boundedValue arity label hlabel edge x).val.edges.length =
      x.1.val.edges.length + x.2.val * occurrences s x.1.val :=
  Occurrence.raw_edges (s + 1) b (extendedArity s arity) s label.val edge.val (x.2.val,x.1)

/-- At most m² added vertices in each one of the m+1 actual positive queries. -/
theorem added_vertices_le (x : BoundedQueries.Input (s + 1) b (extendedArity s arity) s) :
    (boundedValue arity label hlabel edge x).val.vertices.length - x.1.val.vertices.length ≤
      (occurrences s x.1.val) ^ 2 := by
  rw [bounded_vertices, Nat.add_sub_cancel_left, pow_two]
  exact Nat.mul_le_mul_right _ (BoundedQueries.index_le _ _ _ _ x)

/-- At most (m+1)m² added vertices over all m+1 compiled queries. -/
theorem all_added_vertices_le
    (r : FixedGadgetSubstitution.Compiler.Input (s + 1) b (extendedArity s arity)) :
    (∑ k : Fin (occurrences s r.val + 1),
      ((boundedValue arity label hlabel edge ⟨r,k⟩).val.vertices.length - r.val.vertices.length)) ≤
      (occurrences s r.val + 1) * (occurrences s r.val) ^ 2 := by
  calc
    _ ≤ ∑ _k : Fin (occurrences s r.val + 1), (occurrences s r.val) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact added_vertices_le arity label hlabel edge ⟨r,k⟩
    _ = _ := by simp

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.Validated
