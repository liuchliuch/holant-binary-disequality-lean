import Holant.Complexity.FixedGadgetSubstitution.TemplateSemantics
import Holant.Complexity.FixedGadgetSubstitution.TemplateOfNetwork
import Holant.Complexity.ClosedNetworkCompleteness

/-! The fixed literal template serialized from an actual ordinary gadget has
that gadget's exact ordered-boundary denotation under its retained labels. -/
noncomputable section
namespace Holant.Complexity.FixedGadgetSubstitution.Labelling
open RawClosedNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommSemiring K]
variable {n s b : ℕ} {S : NetworkShape n} {arity : ℕ → ℕ}
variable (L : Labelling S s b arity)

abbrev vertexBack : Fin L.template.vertices.length ≃ Fin S.vertices := finCongr L.vertices_length
abbrev edgeBack : Fin L.template.edges.length ≃ Fin S.edges := finCongr L.edges_length

 theorem template_arity (v : Fin L.template.vertices.length) :
    arity (L.template.vertices.get v).1 = S.arity (vertexBack L v) := by
  simp [template,vertexBack,List.get_eq_getElem,L.vertex_arity]
  rfl

 theorem template_route (v : Fin L.template.vertices.length)
    (i : Fin (arity (L.template.vertices.get v).1)) :
    (Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.prodCongr (edgeBack L) (Equiv.refl Bool)))
      (L.template.route L.wellFormed ⟨v,i⟩) =
      S.ports ⟨vertexBack L v,Fin.cast (template_arity L v) i⟩ := by
  apply Template.embed_injective n S.edges
  have he := L.template.embed_route L.wellFormed ⟨v,i⟩
  have hm (q : Fin n ⊕ (Fin L.template.edges.length × Bool)) :
      Template.embed n S.edges
        ((Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.prodCongr (edgeBack L) (Equiv.refl Bool))) q) =
        Template.embed n L.template.edges.length q := by
    cases q <;> rfl
  rw [hm]
  refine he.trans ?_
  simp [Template.portEndpoint,template,vertexBack,List.get_eq_getElem,
    localEndpoint,Template.embed]
  rfl

abbrev assignmentEquiv := Equiv.arrowCongr
  (Equiv.prodCongr (edgeBack L) (Equiv.refl Bool)) (Equiv.refl Bool)

variable (signatures : (i : Fin s) → Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)

/-- The actual original gadget with its literal retained-family labels. -/
def sourceNetwork : Network K n where
  shape := S
  vertex v x := signatures (L.vertex v) (fun i => x (Fin.cast (L.vertex_arity v) i))
  edge e := kernels (L.edge e)

 theorem template_assignment (x : Fin n → Bool)
    (z : (Fin L.template.edges.length × Bool) → Bool)
    (v : Fin L.template.vertices.length) (i : Fin (arity (L.template.vertices.get v).1)) :
    (L.template.network L.wellFormed signatures kernels).shape.assignment x z v i =
      S.assignment x (assignmentEquiv L z) (vertexBack L v) (Fin.cast (template_arity L v) i) := by
  change Sum.elim x z (L.template.route L.wellFormed ⟨v,i⟩) =
    Sum.elim x (assignmentEquiv L z) (S.ports ⟨vertexBack L v,Fin.cast (template_arity L v) i⟩)
  rw [←template_route L v i]
  cases L.template.route L.wellFormed ⟨v,i⟩ <;> simp [assignmentEquiv,edgeBack,Prod.map] <;> rfl

/-- Exact tensor equality for the actual serialized macro, including its full
ordered boundary. This introduces no projective normalization of its own. -/
 theorem denote_template :
    (L.template.network L.wellFormed signatures kernels).denote =
      (sourceNetwork L signatures kernels).denote := by
  funext x
  unfold Network.denote
  apply Fintype.sum_equiv (assignmentEquiv L)
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv (vertexBack L)
    intro v
    apply ClosedLabelling.table_apply_congr signatures
      (show (⟨(L.template.vertices.get v).1,
        (L.wellFormed.1 _ (List.get_mem _ v)).1⟩ : Fin s) = L.vertex (vertexBack L v) from by
        apply Fin.ext
        simp [template,vertexBack,List.get_eq_getElem]
        rfl)
    intro i
    dsimp only [Template.network,sourceNetwork]
    erw [template_assignment L signatures kernels x z v i]
    congr 1
  · apply Fintype.prod_equiv (edgeBack L)
    intro e
    simp [Template.network,sourceNetwork,template,edgeBack,assignmentEquiv,List.get_eq_getElem]
    rfl

/-- Literal vertex and edge labels on an existing physical network are enough
to recover its exact tensor from the fixed compiled template. -/
 theorem denote_template_of_labels
    (vertex : (v : Fin S.vertices) → Signature K (S.arity v))
    (edge : Fin S.edges → Bool → Bool → K)
    (hv : ∀v x,(sourceNetwork L signatures kernels).vertex v x=vertex v x)
    (he : ∀e a b,(sourceNetwork L signatures kernels).edge e a b=edge e a b) :
    (L.template.network L.wellFormed signatures kernels).denote=(Network.mk S vertex edge).denote := by
  rw [denote_template]
  exact Network.denote_congr S _ vertex _ edge hv he

end Holant.Complexity.FixedGadgetSubstitution.Labelling
