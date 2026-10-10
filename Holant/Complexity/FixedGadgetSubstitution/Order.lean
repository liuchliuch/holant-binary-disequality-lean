import Holant.Complexity.FixedGadgetSubstitution.RawIndex

/-! Explicit ordinal enumerations of the generated vertex and edge blocks. -/
namespace Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork
set_option backward.isDefEq.respectTransparency false

def vertexOrder (templates : ℕ → Template) (r : RawClosedNetwork) :
    Fin (replace templates r).vertices.length ≃ Blocks (vertexSize templates) r.vertices :=
  (finCongr (replace_vertex_count templates r)).trans (blockEquiv (vertexSize templates) r.vertices).symm

def edgeOrder (templates : ℕ → Template) (r : RawClosedNetwork) :
    Fin (replace templates r).edges.length ≃
      (Fin r.edges.length ⊕ Blocks (edgeSize templates) r.vertices) :=
  (finCongr (replace_edge_count templates r)).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _)
      (blockEquiv (edgeSize templates) r.vertices).symm))

@[simp] theorem vertexOrder_symm_val (templates : ℕ → Template) (r : RawClosedNetwork)
    (p : Blocks (vertexSize templates) r.vertices) :
    ((vertexOrder templates r).symm p).val = (blockEquiv (vertexSize templates) r.vertices p).val := rfl

@[simp] theorem edgeOrder_symm_old (templates : ℕ → Template) (r : RawClosedNetwork)
    (e : Fin r.edges.length) : ((edgeOrder templates r).symm (.inl e)).val = e.val := rfl

@[simp] theorem edgeOrder_symm_new (templates : ℕ → Template) (r : RawClosedNetwork)
    (p : Blocks (edgeSize templates) r.vertices) :
    ((edgeOrder templates r).symm (.inr p)).val =
      edgeOffset templates r.edges.length r.vertices p.1 + p.2.val := by
  change r.edges.length + (blockEquiv (edgeSize templates) r.vertices p).val = _
  exact new_edge_index templates r.edges.length r.vertices p

 theorem vertex_at_order (templates : ℕ → Template) (r : RawClosedNetwork)
    (p : Blocks (vertexSize templates) r.vertices) :
    (replace templates r).vertices.get ((vertexOrder templates r).symm p) =
      ((templates (r.vertices.get p.1).1).placeVertices
        (edgeOffset templates r.edges.length r.vertices p.1) (r.vertices.get p.1).2).get
          (Fin.cast (by simp [vertexSize]) p.2) := by
  exact expandRows_vertex_at templates r.edges.length r.vertices p

 theorem edge_at_order_old (templates : ℕ → Template) (r : RawClosedNetwork)
    (e : Fin r.edges.length) :
    (replace templates r).edges.get ((edgeOrder templates r).symm (.inl e)) = r.edges.get e := by
  simp only [replace,List.get_eq_getElem,edgeOrder_symm_old]
  exact List.getElem_append_left e.isLt

 theorem edge_at_order_new (templates : ℕ → Template) (r : RawClosedNetwork)
    (p : Blocks (edgeSize templates) r.vertices) :
    (replace templates r).edges.get ((edgeOrder templates r).symm (.inr p)) =
      (templates (r.vertices.get p.1).1).edges.get p.2 := by
  change (r.edges ++ (expandRows templates r.edges.length r.vertices).edges).get
    ((edgeOrder templates r).symm (.inr p)) = _
  simp only [List.get_eq_getElem]
  change (r.edges ++ (expandRows templates r.edges.length r.vertices).edges)[r.edges.length+(blockEquiv (edgeSize templates) r.vertices p).val]'(by exact ((edgeOrder templates r).symm (.inr p)).isLt) = _
  rw [List.getElem_append_right (by omega)]
  simpa using expandRows_edge_at templates r.edges.length r.vertices p

end Holant.Complexity.FixedGadgetSubstitution
