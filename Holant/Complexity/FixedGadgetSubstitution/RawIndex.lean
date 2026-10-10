import Holant.Complexity.FixedGadgetSubstitution.BlockIndex

/-! Literal record lookups at the cumulative block indices. -/
namespace Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork
set_option backward.isDefEq.respectTransparency false

abbrev vertexSize (templates : ℕ → Template) (row : RawVertex) := (templates row.1).vertices.length
abbrev edgeSize (templates : ℕ → Template) (row : RawVertex) := (templates row.1).edges.length

def edgeOffset (templates : ℕ → Template) (offset : ℕ) (rows : List RawVertex)
    (v : Fin rows.length) : ℕ := offset + ((rows.take v.val).map (edgeSize templates)).sum

 theorem expandRows_vertex_at (templates : ℕ → Template) (offset : ℕ) (rows : List RawVertex)
    (p : Blocks (vertexSize templates) rows) :
    (expandRows templates offset rows).vertices[(blockEquiv (vertexSize templates) rows p).val]'(by
      rw [expandRows_vertex_count]
      exact (blockEquiv (vertexSize templates) rows p).isLt) =
    ((templates (rows.get p.1).1).placeVertices
      (edgeOffset templates offset rows p.1) (rows.get p.1).2).get
        (Fin.cast (by simp [vertexSize]) p.2) := by
  induction rows generalizing offset with
  | nil => exact Fin.elim0 p.1
  | cons row rows ih =>
    rcases p with ⟨i,j⟩
    induction i using Fin.cases with
    | zero =>
      change Fin (templates row.1).vertices.length at j
      have hj : j.val < ((templates row.1).placeVertices offset row.2).length := by simpa using j.isLt
      simp only [blockEquiv_val,Fin.val_zero,List.take_zero,List.map_nil,List.sum_nil,
        Nat.zero_add,expandRows,edgeOffset]
      simp only [List.get_eq_getElem,List.getElem_cons_zero,Fin.val_zero,List.take_zero,
        List.map_nil,List.sum_nil,Nat.add_zero]
      rw [List.getElem_append_left hj]
      rfl
    | succ i =>
      have hi := ih (offset+(templates row.1).edges.length) ⟨i,j⟩
      simp only [blockEquiv_val] at hi ⊢
      simp only [Fin.val_succ,List.take_succ_cons,List.map_cons,List.sum_cons,
        expandRows,vertexSize,edgeOffset,List.get_eq_getElem,List.getElem_cons_succ,
        Nat.add_assoc] at hi ⊢
      rw [List.getElem_append_right (by simp only [Template.placeVertices_length]; omega)]
      simpa [edgeSize] using hi

 theorem expandRows_edge_at (templates : ℕ → Template) (offset : ℕ) (rows : List RawVertex)
    (p : Blocks (edgeSize templates) rows) :
    (expandRows templates offset rows).edges[(blockEquiv (edgeSize templates) rows p).val]'(by
      rw [expandRows_edges,List.length_flatten,List.map_map]
      exact (blockEquiv (edgeSize templates) rows p).isLt) =
      (templates (rows.get p.1).1).edges.get p.2 := by
  simpa only [expandRows_edges] using get_flatten_blocks rows (fun row => (templates row.1).edges) p

/-- The generated edge ID is exactly the compiler's cumulative offset. -/
 theorem new_edge_index (templates : ℕ → Template) (offset : ℕ) (rows : List RawVertex)
    (p : Blocks (edgeSize templates) rows) :
    offset + (blockEquiv (edgeSize templates) rows p).val =
      edgeOffset templates offset rows p.1 + p.2.val := by
  rw [blockEquiv_val]
  simp [edgeOffset,Nat.add_assoc]

end Holant.Complexity.FixedGadgetSubstitution
