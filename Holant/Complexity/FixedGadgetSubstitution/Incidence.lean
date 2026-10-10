import Holant.Complexity.FixedGadgetSubstitution.Order
import Holant.Complexity.FixedGadgetSubstitution.TemplateSemantics

/-! The generated query's ordered port lookup is the literal original-port
attachment or the exact cumulative local-edge attachment. -/
namespace Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork
set_option backward.isDefEq.respectTransparency false

abbrev sourceArity (templates : ℕ → Template) (label : ℕ) := (templates label).boundary

variable (templates : ℕ → Template) (r : RawClosedNetwork)

abbrev localVertex (p : Blocks (vertexSize templates) r.vertices) : LocalVertex :=
  (templates (r.vertices.get p.1).1).vertices.get p.2

 theorem vertex_record (p : Blocks (vertexSize templates) r.vertices) :
    (replace templates r).vertices.get ((vertexOrder templates r).symm p) =
      ((localVertex templates r p).1,(localVertex templates r p).2.map
        (Template.placeEndpoint (edgeOffset templates r.edges.length r.vertices p.1)
          (r.vertices.get p.1).2)) := by
  rw [vertex_at_order]
  simp [Template.placeVertices,List.get_eq_getElem]

 theorem vertex_label (p : Blocks (vertexSize templates) r.vertices) :
    ((replace templates r).vertices.get ((vertexOrder templates r).symm p)).1 =
      (localVertex templates r p).1 := congrArg Prod.fst (vertex_record templates r p)

variable {sourceCount s b : ℕ} {arity : ℕ → ℕ}
variable (hr : r.WellFormed sourceCount b (sourceArity templates))
variable (hg : ∀ label < sourceCount, (templates label).WellFormed s b arity)

 include hr hg in
 theorem query_wellFormed : (replace templates r).WellFormed s b arity :=
  replace_wellFormed templates r hr (fun label hlabel => ⟨hg label hlabel,rfl⟩)

abbrev localWellFormed (v : Fin r.vertices.length) :
    (templates (r.vertices.get v).1).WellFormed s b arity := hg _ (hr.1 v).1

def queryPort (p : Blocks (vertexSize templates) r.vertices)
    (i : Fin (arity (localVertex templates r p).1)) : (replace templates r).Ports arity :=
  ⟨(vertexOrder templates r).symm p,
    Fin.cast (congrArg arity (vertex_label templates r p).symm) i⟩

 theorem query_portEndpoint (p : Blocks (vertexSize templates) r.vertices)
    (i : Fin (arity (localVertex templates r p).1)) :
    (replace templates r).portEndpoint (query_wellFormed templates r hr hg) (queryPort templates r p i) =
      Template.placeEndpoint (edgeOffset templates r.edges.length r.vertices p.1)
        (r.vertices.get p.1).2
        ((templates (r.vertices.get p.1).1).portEndpoint (localWellFormed templates r hr hg p.1) ⟨p.2,i⟩) := by
  dsimp only [RawClosedNetwork.portEndpoint,queryPort]
  have hv := vertex_record templates r p
  simp only [List.get_eq_getElem,vertexOrder_symm_val] at hv
  simp only [List.get_eq_getElem,vertexOrder_symm_val]
  simp only [Fin.val_cast,hv,List.getElem_map]
  simp [Template.portEndpoint,List.get_eq_getElem]

/-- The finite attachment route, with old and copy-local edge IDs distinguished. -/
def attachment (p : Blocks (vertexSize templates) r.vertices)
    (i : Fin (arity (localVertex templates r p).1)) :
    (Fin r.edges.length ⊕ Blocks (edgeSize templates) r.vertices) × Bool :=
  match (templates (r.vertices.get p.1).1).route (localWellFormed templates r hr hg p.1) ⟨p.2,i⟩ with
  | .inl j => let e := r.route hr ⟨p.1,j⟩; (.inl e.1,e.2)
  | .inr e => (.inr ⟨p.1,e.1⟩,e.2)

 theorem attachment_numeric (p : Blocks (vertexSize templates) r.vertices)
    (i : Fin (arity (localVertex templates r p).1)) :
    (((edgeOrder templates r).symm (attachment templates r hr hg p i).1).val,
      (attachment templates r hr hg p i).2) =
      Template.placeEndpoint (edgeOffset templates r.edges.length r.vertices p.1)
        (r.vertices.get p.1).2
        ((templates (r.vertices.get p.1).1).portEndpoint (localWellFormed templates r hr hg p.1) ⟨p.2,i⟩) := by
  have he := (templates (r.vertices.get p.1).1).embed_route
    (localWellFormed templates r hr hg p.1) ⟨p.2,i⟩
  unfold attachment
  cases h : (templates (r.vertices.get p.1).1).route
      (localWellFormed templates r hr hg p.1) ⟨p.2,i⟩ with
  | inl j =>
    rw [h] at he
    rw [←he]
    simp only [Template.embed,Sum.elim_inl,Template.placeEndpoint,
      edgeOrder_symm_old,RawClosedNetwork.route,RawClosedNetwork.portEndpoint]
    have hj : j.val < (r.vertices.get p.1).2.length := by rw [(hr.1 p.1).2]; exact j.isLt
    simp only [List.get_eq_getElem]
    simp only [List.get_eq_getElem] at hj
    rw [List.getD_eq_getElem _ _ hj]
    rfl
  | inr e =>
    rw [h] at he
    rw [←he]
    simp [Template.embed,Template.placeEndpoint]

/-- Exact decoded incidence agrees with physical substitution, including the
Boolean end orientation of each original loop or parallel edge. -/
 theorem query_route (p : Blocks (vertexSize templates) r.vertices)
    (i : Fin (arity (localVertex templates r p).1)) :
    ((edgeOrder templates r)
      ((replace templates r).route (query_wellFormed templates r hr hg) (queryPort templates r p i)).1,
      ((replace templates r).route (query_wellFormed templates r hr hg) (queryPort templates r p i)).2) =
      attachment templates r hr hg p i := by
  have hv := query_portEndpoint templates r hr hg p i
  have he := attachment_numeric templates r hr hg p i
  have hp : (replace templates r).route (query_wellFormed templates r hr hg)
      (queryPort templates r p i) =
      ((edgeOrder templates r).symm (attachment templates r hr hg p i).1,
        (attachment templates r hr hg p i).2) := by
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst (hv.trans he.symm)
    · exact congrArg (fun p : RawEndpoint => p.2) (hv.trans he.symm)
  rw [hp]
  simp

end Holant.Complexity.FixedGadgetSubstitution
