import Holant.Proofs.Tractability.EOEvaluation.CandidateExecution.Graph


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Semantics
open Holant.Tractable Holant.Complexity
open scoped BigOperators
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ} (D : Source.Family s arity)
set_option backward.isDefEq.respectTransparency false

def label (x : Graph.Input (s := s) (arity := arity)) (v : Fin x.1.val.vertices.length) :
    Catalogue.Label (s := s) (arity := arity) :=
  Records.candidate (x, v.val, x.1.val.vertices.get v) (x.1.val.signatureLabel x.1.property v)
def labelled (x : Graph.Input (s := s) (arity := arity)) : Network AlgebraicComplex 0 where
  shape := (Source.network D x.1).shape
  vertex v := Catalogue.tensor D (label x v)
  edge := (Source.network D x.1).edge
def target (x : Graph.Input (s := s) (arity := arity)) : Network AlgebraicComplex 0 :=
  (Graph.value x).val.realize (Graph.value x).property (Catalogue.signatures D) Catalogue.kernels

theorem vertex_label (x : Graph.Input (s := s) (arity := arity)) (v : Fin x.1.val.vertices.length) :
    (Graph.raw x).signatureLabel (Graph.wellFormed x) (Graph.vertexIndex x v) = Catalogue.codes (label x v) := by
  apply Fin.ext
  change ((Graph.raw x).vertices.get (Graph.vertexIndex x v)).1 = _
  rw [Graph.vertex_get]
  exact Records.label_valid _ (x.1.property.1 v).1

theorem route (x : Graph.Input (s := s) (arity := arity)) (v : Fin x.1.val.vertices.length)
    (j : Fin (arity (x.1.val.vertices.get v).1)) :
    (Graph.raw x).route (Graph.wellFormed x)
      ⟨Graph.vertexIndex x v, Fin.cast (Graph.vertex_arity x v).symm j⟩ =
        x.1.val.route x.1.property ⟨v, j⟩ := by
  have hp : (Graph.raw x).portEndpoint (Graph.wellFormed x)
      ⟨Graph.vertexIndex x v, Fin.cast (Graph.vertex_arity x v).symm j⟩ =
        x.1.val.portEndpoint x.1.property ⟨v, j⟩ := by
    have hports := congrArg Prod.snd (Graph.vertex_get x v)
    simp only [Records.vertex] at hports
    simp only [RawClosedNetwork.portEndpoint, List.get_eq_getElem, Fin.val_cast]
    simp only [List.get_eq_getElem] at hports
    simp only [hports]
  apply Prod.ext
  · apply Fin.ext
    simpa only [RawClosedNetwork.route] using congrArg Prod.fst hp
  · simpa only [RawClosedNetwork.route] using congrArg Prod.snd hp

theorem assignment_port (x : Graph.Input (s := s) (arity := arity))
    (z : (Fin x.1.val.edges.length × Bool) → Bool) (v : Fin x.1.val.vertices.length)
    (j : Fin (arity (x.1.val.vertices.get v).1)) :
    (target D x).shape.assignment Fin.elim0 z (Graph.vertexIndex x v)
      (Fin.cast (Graph.vertex_arity x v).symm j) =
        (labelled D x).shape.assignment Fin.elim0 z v j := by
  change z ((Graph.raw x).route (Graph.wellFormed x)
      ⟨Graph.vertexIndex x v, Fin.cast (Graph.vertex_arity x v).symm j⟩) =
    z (x.1.val.route x.1.property ⟨v,j⟩)
  rw [route]

theorem vertex_term (x : Graph.Input (s := s) (arity := arity))
    (z : (Fin x.1.val.edges.length × Bool) → Bool) (v : Fin x.1.val.vertices.length) :
    (target D x).vertex (Graph.vertexIndex x v)
      ((target D x).shape.assignment Fin.elim0 z (Graph.vertexIndex x v)) =
        (labelled D x).vertex v ((labelled D x).shape.assignment Fin.elim0 z v) := by
  let i := (Graph.raw x).signatureLabel (Graph.wellFormed x) (Graph.vertexIndex x v)
  let w := (target D x).shape.assignment Fin.elim0 z (Graph.vertexIndex x v)
  change Catalogue.signatures D i w = Catalogue.tensor D (label x v) _
  rw [Catalogue.vertex_lookup D i (label x v) (vertex_label x v) w]
  congr 1
  funext j
  exact assignment_port D x z v j

theorem term (x : Graph.Input (s := s) (arity := arity))
    (z : (Fin x.1.val.edges.length × Bool) → Bool) :
    (target D x).assignmentTerm Fin.elim0 z = (labelled D x).assignmentTerm Fin.elim0 z := by
  have hv := (Graph.vertexIndex x).prod_comp (fun v =>
    (target D x).vertex v ((target D x).shape.assignment Fin.elim0 z v))
  unfold Network.assignmentTerm
  exact congrArg₂ (· * ·)
    (hv.symm.trans (Finset.prod_congr rfl (fun v _ => vertex_term D x z v))) rfl

theorem realizes (x : Graph.Input (s := s) (arity := arity)) :
    (target D x).denote Fin.elim0 = (labelled D x).denote Fin.elim0 := by
  change (∑ z, (target D x).assignmentTerm Fin.elim0 z) = ∑ z, (labelled D x).assignmentTerm Fin.elim0 z
  exact Finset.sum_congr rfl (fun z _ => term D x z)

theorem true_labelled (r : Source.Input (s := s) (arity := arity)) :
    labelled D (r, Responses.truth D r) = CandidatePairing.paired D r := by
  have hv : (fun v => Catalogue.tensor D (label (r, Responses.truth D r) v)) =
      (fun v => PairLift.restrict (CandidatePairing.pairing D r v) ((Source.network D r).vertex v)) := by
    funext v
    dsimp only [label, Records.candidate, Catalogue.tensor, RawClosedNetwork.signatureLabel]
    simp only [Responses.mask_truth D r v, (CandidatePairing.label_spec D r v).1]
    rfl
  exact congrArg (fun f => Network.mk (Source.network D r).shape f
    (Source.network D r).edge) hv

theorem true_denote (r : Source.Input (s := s) (arity := arity)) :
    (target D (r, Responses.truth D r)).denote Fin.elim0 = (Source.network D r).denote Fin.elim0 := by
  rw [realizes, true_labelled, CandidatePairing.denote_eq]

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Semantics
