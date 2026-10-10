import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.Compiler
import Holant.Proofs.Algorithms.LocalAffine.NetworkGauge


namespace Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Semantics

open Holant.Tractable Holant.Complexity FixedGadgetSubstitution.Compiler ProductMachine
open MainChain
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)

def source (x : Graph.Input (s := s) (b := b) (arity := arity)) := LocalAffineLabels.network D x.1
def target (x : Graph.Input (s := s) (b := b) (arity := arity)) :=
  (Graph.value x).val.realize (Graph.value x).property (Catalogue.family D).signatures (Catalogue.family D).kernels

def Supported (x : Graph.Input (s := s) (b := b) (arity := arity)) : Prop :=
  (source D x).assignmentTerm Fin.elim0 (Graph.reference x) ≠ 0

theorem local_vertex_word (x : Graph.Input (s := s) (b := b) (arity := arity))
    (v : Fin x.1.val.vertices.length) :
    LocalWords.sample (arity (x.1.val.vertices.get v).1) (x.2, (x.1.val.vertices.get v).2) =
      (source D x).shape.assignment Fin.elim0 (Graph.reference x) v := by
  funext j
  simp only [source, LocalAffineLabels.network, RawClosedNetwork.realize, NetworkShape.assignment,
    RawClosedNetwork.shape_ports, Sum.elim_inr, LocalWords.sample, Graph.reference]
  rw [RawFamily.vertex_ports s b arity x.1 v j]
  rfl

theorem local_edge_word (x : Graph.Input (s := s) (b := b) (arity := arity))
    (e : Fin x.1.val.edges.length) :
    LocalWords.edgeSample (x.2, e.val) = ![Graph.reference x (e, false), Graph.reference x (e, true)] := by
  funext j; fin_cases j <;> rfl

theorem vertex_label (x : Graph.Input (s := s) (b := b) (arity := arity))
    (v : Fin x.1.val.vertices.length) :
    (Graph.raw x).signatureLabel (Graph.wellFormed x) (Graph.vertexIndex x v) =
      Catalogue.vertexEquiv (LocalAffineLabels.vertexLabel D x.1 (Graph.reference x) v) := by
  apply Fin.ext
  change ((Graph.raw x).vertices.get (Graph.vertexIndex x v)).1 = _
  rw [Graph.vertex_get]
  change Records.vertexLabel (s := s) (arity := arity) (x.2,x.1.val.vertices.get v) = _
  rw [Records.vertex_label (x.2,x.1.val.vertices.get v) (x.1.property.1 v).1]
  simp only [Records.vertexCandidate,
    Catalogue.vertexCode, local_vertex_word, LocalAffineLabels.vertexLabel, source,
    RawClosedNetwork.signatureLabel]
  exact congrArg (fun w => (Catalogue.vertexEquiv
    ⟨⟨(x.1.val.vertices.get v).1,(x.1.property.1 v).1⟩,w⟩).val) (local_vertex_word D x v)

theorem edge_label (x : Graph.Input (s := s) (b := b) (arity := arity))
    (e : Fin x.1.val.edges.length) :
    (Graph.raw x).edgeLabel (Graph.wellFormed x) (Graph.edgeIndex x e) =
      Catalogue.edgeEquiv (LocalAffineLabels.edgeLabel D x.1 (Graph.reference x) e) := by
  apply Fin.ext
  change (Graph.raw x).edges.get (Graph.edgeIndex x e) = _
  rw [Graph.edge_get, Records.edge_label _ (x.1.property.2.1 e)]
  simp only [Records.edgeCandidate, Catalogue.edgeCode, local_edge_word,
    LocalAffineLabels.edgeLabel, RawClosedNetwork.edgeLabel]

def arity_eq (x : Graph.Input (s := s) (b := b) (arity := arity)) (v : Fin x.1.val.vertices.length) :
    Catalogue.targetArity (s := s) (arity := arity) ((Graph.raw x).vertices.get (Graph.vertexIndex x v)).1 =
      arity (x.1.val.vertices.get v).1 := (Graph.vertex_range_arity x v).2

theorem route (x : Graph.Input (s := s) (b := b) (arity := arity))
    (v : Fin x.1.val.vertices.length) (j : Fin (arity (x.1.val.vertices.get v).1)) :
    (Graph.raw x).route (Graph.wellFormed x) ⟨Graph.vertexIndex x v, Fin.cast (arity_eq x v).symm j⟩ =
      (Graph.edgeIndex x (x.1.val.route x.1.property ⟨v, j⟩).1, (x.1.val.route x.1.property ⟨v, j⟩).2) := by
  have hp : (Graph.raw x).portEndpoint (Graph.wellFormed x)
      ⟨Graph.vertexIndex x v, Fin.cast (arity_eq x v).symm j⟩ =
        x.1.val.portEndpoint x.1.property ⟨v, j⟩ := by
    have hr := congrArg Prod.snd (Graph.vertex_get x v)
    simp only [Records.vertex] at hr
    simp only [RawClosedNetwork.portEndpoint, List.get_eq_getElem, Fin.val_cast]
    simp only [List.get_eq_getElem] at hr
    simp only [hr]
  apply Prod.ext
  · apply Fin.ext
    simpa [RawClosedNetwork.route, Graph.edgeIndex] using congrArg Prod.fst hp
  · simpa only [RawClosedNetwork.route] using congrArg Prod.snd hp

def assignments (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    ((Fin x.1.val.edges.length × Bool) → Bool) ≃ ((Fin (Graph.raw x).edges.length × Bool) → Bool) :=
  Equiv.arrowCongr (Equiv.prodCongr (Graph.edgeIndex x) (Equiv.refl Bool)) (Equiv.refl Bool)

@[simp] theorem assignments_apply (x : Graph.Input (s := s) (b := b) (arity := arity))
    (z : (Fin x.1.val.edges.length × Bool) → Bool) (e : Fin x.1.val.edges.length) (side : Bool) :
    assignments x z (Graph.edgeIndex x e, side) = z (e, side) := by simp [assignments]

theorem assignment_port (x : Graph.Input (s := s) (b := b) (arity := arity))
    (z : (Fin x.1.val.edges.length × Bool) → Bool) (v : Fin x.1.val.vertices.length)
    (j : Fin (arity (x.1.val.vertices.get v).1)) :
    (target D x).shape.assignment Fin.elim0 (assignments x z) (Graph.vertexIndex x v)
        (Fin.cast (arity_eq x v).symm j) = (source D x).shape.assignment Fin.elim0 z v j := by
  change assignments x z ((Graph.raw x).route (Graph.wellFormed x)
    ⟨Graph.vertexIndex x v, Fin.cast (arity_eq x v).symm j⟩) =
      z (x.1.val.route x.1.property ⟨v,j⟩)
  rw [route, assignments_apply]

theorem vertex_term (x : Graph.Input (s := s) (b := b) (arity := arity))
    (z : (Fin x.1.val.edges.length × Bool) → Bool) (v : Fin x.1.val.vertices.length) :
    (target D x).vertex (Graph.vertexIndex x v)
      ((target D x).shape.assignment Fin.elim0 (assignments x z) (Graph.vertexIndex x v)) =
        (LocalAffineLabels.labelled D x.1 (Graph.reference x)).vertex v
          ((source D x).shape.assignment Fin.elim0 z v) := by
  let i := (Graph.raw x).signatureLabel (Graph.wellFormed x) (Graph.vertexIndex x v)
  let a := LocalAffineLabels.vertexLabel D x.1 (Graph.reference x) v
  let w := (target D x).shape.assignment Fin.elim0 (assignments x z) (Graph.vertexIndex x v)
  have hl : i = Catalogue.vertexEquiv a := vertex_label D x v
  change (Catalogue.family D).signatures i w =
    LocalAffineLabels.vertex D a ((source D x).shape.assignment Fin.elim0 z v)
  rw [Catalogue.vertex_lookup D i a hl w]
  congr 1
  funext j
  exact assignment_port D x z v j

theorem edge_term (x : Graph.Input (s := s) (b := b) (arity := arity))
    (z : (Fin x.1.val.edges.length × Bool) → Bool) (e : Fin x.1.val.edges.length) :
    (target D x).edge (Graph.edgeIndex x e)
      (assignments x z (Graph.edgeIndex x e, false)) (assignments x z (Graph.edgeIndex x e, true)) =
        (LocalAffineLabels.labelled D x.1 (Graph.reference x)).edge e (z (e, false)) (z (e, true)) := by
  change (Catalogue.family D).kernels
    ((Graph.raw x).edgeLabel (Graph.wellFormed x) (Graph.edgeIndex x e))
    (assignments x z (Graph.edgeIndex x e,false)) (assignments x z (Graph.edgeIndex x e,true)) = _
  rw [edge_label, assignments_apply, assignments_apply, Catalogue.edge_value]
  rfl

/-- Strong realization identity: equality of every assignment term after
identity-on-numeric-IDs reindexing, not only equality of partition sums. -/
theorem realizes_term (x : Graph.Input (s := s) (b := b) (arity := arity))
    (z : (Fin x.1.val.edges.length × Bool) → Bool) :
    (target D x).assignmentTerm Fin.elim0 (assignments x z) =
      (LocalAffineLabels.labelled D x.1 (Graph.reference x)).assignmentTerm Fin.elim0 z := by
  have hv := (Graph.vertexIndex x).prod_comp (fun v =>
    (target D x).vertex v ((target D x).shape.assignment Fin.elim0 (assignments x z) v))
  have he := (Graph.edgeIndex x).prod_comp (fun e =>
    (target D x).edge e (assignments x z (e, false)) (assignments x z (e, true)))
  unfold Network.assignmentTerm
  apply (congrArg₂ (· * ·) hv he).symm.trans
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    exact vertex_term D x z v
  · apply Finset.prod_congr rfl
    intro e _
    exact edge_term D x z e

theorem realizes (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    (target D x).denote Fin.elim0 =
      (LocalAffineLabels.labelled D x.1 (Graph.reference x)).denote Fin.elim0 := by
  change (∑ z, (target D x).assignmentTerm Fin.elim0 z) =
    ∑ z, (LocalAffineLabels.labelled D x.1 (Graph.reference x)).assignmentTerm Fin.elim0 z
  apply ((assignments x).sum_comp (fun z => (target D x).assignmentTerm Fin.elim0 z)).symm.trans
  exact Finset.sum_congr rfl (fun z _ => realizes_term D x z)

theorem supported_denote (x : Graph.Input (s := s) (b := b) (arity := arity)) (hx : Supported D x) :
    (target D x).denote Fin.elim0 = (source D x).denote Fin.elim0 := by
  rw [realizes, LocalAffineLabels.labelled_eq_gauged D x.1 (Graph.reference x) hx]
  exact LocalAffineNetwork.denote_gauged _ _

/-- Unsupported references choose at least one of the literal zero tensors
already present in the finite alphabet. This is a semantic failure identity,
not a runtime support search or a none/some controller. -/
theorem unsupported_labelled_zero (x : Graph.Input (s := s) (b := b) (arity := arity))
    (hx : ¬ Supported D x) :
    (LocalAffineLabels.labelled D x.1 (Graph.reference x)).denote Fin.elim0 = 0 := by
  classical
  have hz : (source D x).assignmentTerm Fin.elim0 (Graph.reference x) = 0 := not_ne_iff.mp hx
  unfold Network.assignmentTerm at hz
  rcases mul_eq_zero.mp hz with hv | he
  · obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hv
    have hf : D.signatures (x.1.val.signatureLabel x.1.property v)
        ((source D x).shape.assignment Fin.elim0 (Graph.reference x) v) = 0 := hv
    change D.signatures (x.1.val.signatureLabel x.1.property v)
      ((LocalAffineLabels.network D x.1).shape.assignment Fin.elim0 (Graph.reference x) v) = 0 at hf
    have localZero (w) : (LocalAffineLabels.labelled D x.1 (Graph.reference x)).vertex v w = 0 := by
      simp [LocalAffineLabels.labelled, LocalAffineLabels.vertex, LocalAffineLabels.vertexLabel,
        source, hf]
    have productZero (z : (Fin x.1.val.edges.length × Bool) → Bool) :
        (∏ u, (LocalAffineLabels.labelled D x.1 (Graph.reference x)).vertex u
          ((LocalAffineLabels.labelled D x.1 (Graph.reference x)).shape.assignment Fin.elim0 z u)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (localZero _)
    simp only [Network.denote, Network.assignmentTerm]
    simp only [productZero, zero_mul, mul_zero, Finset.sum_const_zero]
  · obtain ⟨e, _, he⟩ := Finset.prod_eq_zero_iff.mp he
    have hf : kernelSignature (D.kernels (x.1.val.edgeLabel x.1.property e))
        ![Graph.reference x (e, false), Graph.reference x (e, true)] = 0 := he
    have localZero (u v : Bool) :
        (LocalAffineLabels.labelled D x.1 (Graph.reference x)).edge e u v = 0 := by
      simp [LocalAffineLabels.labelled, LocalAffineLabels.edge, LocalAffineLabels.edgeLabel, hf]
    have productZero (z : (Fin x.1.val.edges.length × Bool) → Bool) :
        (∏ e, (LocalAffineLabels.labelled D x.1 (Graph.reference x)).edge e (z (e, false)) (z (e, true))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (localZero _ _)
    simp only [Network.denote, Network.assignmentTerm]
    simp only [productZero, zero_mul, mul_zero, Finset.sum_const_zero]

end
end Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Semantics
