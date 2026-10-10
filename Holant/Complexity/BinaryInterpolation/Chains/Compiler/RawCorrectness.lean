import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Assemble
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Correctness
import Holant.Complexity.FixedGadgetSubstitution.Identity

/-! The output physically emitted by the dynamic Boolean program is exactly
ordinary template substitution in the original graph, in its original row and
boundary order. Fresh-edge offsets use only actual earlier marked occurrences.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
open FixedGadgetSubstitution RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384

def templates (arity : ℕ → ℕ) (distinguished label edge k i : ℕ) : Template :=
  if i = distinguished then explicitTemplate label edge k else identityTemplate arity i

@[simp] theorem template_edges (arity : ℕ → ℕ) (distinguished label edge k i : ℕ) :
    (templates arity distinguished label edge k i).edges.length =
      if i = distinguished then k else 0 := by
  by_cases h : i = distinguished <;> simp [templates,h,identityTemplate]

theorem prefix_edges (arity : ℕ → ℕ) (distinguished label edge k : ℕ) (rs : List RawVertex) :
    (rs.map (fun row => (templates arity distinguished label edge k row.1).edges.length)).sum =
      k * (rs.map (fun row => if row.1 = distinguished then 1 else 0)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons,List.sum_cons,template_edges] at ih ⊢
    by_cases h : r.1 = distinguished <;>
      simp [h,ih,Nat.mul_add,Nat.add_comm]

theorem identity_place (arity : ℕ → ℕ) (row : RawVertex) (offset : ℕ)
    (hr : row.2.length = arity row.1) :
    (identityTemplate arity row.1).placeVertices offset row.2 = [row] := by
  rcases row with ⟨label,boundary⟩
  have hb := map_range_getD boundary (0,false)
  rw [Labelling.map_range_eq_ofFn] at hb
  simpa only [identityTemplate,Template.placeVertices,List.ofFn_succ,List.ofFn_zero,
    List.map_cons,List.map_nil,List.map_ofFn,Template.placeEndpoint,←hr,
    Function.comp_def,Fin.coe_cast] using
      congrArg (fun xs => [(label,xs)]) hb

variable (s b : ℕ) (arity : ℕ → ℕ)

theorem offset_eq (distinguished label edge : ℕ) (x : Query s b arity) :
    offset s b arity distinguished x =
      x.1.2.val.edges.length +
        ((x.1.2.val.vertices.take x.2.val).map (fun row =>
          (templates arity distinguished label edge x.1.1 row.1).edges.length)).sum := by
  rw [prefix_edges]
  rfl

theorem rows_eq_place (distinguished label edge : ℕ) (x : Query s b arity) :
    rows s b arity distinguished label x =
      (templates arity distinguished label edge x.1.1 (x.1.2.val.vertices.get x.2).1).placeVertices
        (offset s b arity distinguished x) (x.1.2.val.vertices.get x.2).2 := by
  by_cases h : (x.1.2.val.vertices.get x.2).1 = distinguished
  · simpa only [rows,marked,h,decide_true,ite_true,templates,placement] using
      placedRows_eq label edge (placement s b arity distinguished x)
  · simp only [rows,marked,h,decide_false,ite_false,templates]
    exact (identity_place arity _ _ (x.1.2.property.1 x.2).2).symm

theorem edgeRows_eq (distinguished label edge : ℕ) (x : Query s b arity) :
    edgeRows s b arity distinguished edge x =
      (templates arity distinguished label edge x.1.1 (x.1.2.val.vertices.get x.2).1).edges := by
  by_cases h : (x.1.2.val.vertices.get x.2).1 = distinguished <;>
    simp only [edgeRows,marked,h,decide_true,decide_false,ite_true,ite_false,templates,
      explicitTemplate,identityTemplate,Bool.false_eq_true]

/-- Literal equality of full ordered raw records, not merely equal values. -/
theorem raw_eq_replace (distinguished label edge : ℕ) (x : Input s b arity) :
    raw s b arity distinguished label edge x =
      replace (templates arity distinguished label edge x.1) x.2.val := by
  unfold raw replace
  congr 1
  · rw [FixedGadgetSubstitution.Compiler.expandRows_vertices_indexed]
    apply List.flatMap_congr
    intro i _
    rw [rows_eq_place s b arity distinguished label edge,offset_eq s b arity distinguished label edge]
  · rw [←FixedGadgetSubstitution.Compiler.indexed_edges]
    apply congrArg (x.2.val.edges ++ ·)
    apply List.flatMap_congr
    intro i _
    exact edgeRows_eq s b arity distinguished label edge ⟨x,i⟩

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
