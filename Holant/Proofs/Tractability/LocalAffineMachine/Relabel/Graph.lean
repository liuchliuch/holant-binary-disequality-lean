import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.Records
import Holant.Proofs.Tractability.ProductMachine.RawFamily


namespace Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Graph

open Holant.Tractable Holant.Tractable.AffinePhase Holant.Complexity FixedGadgetSubstitution.Compiler ProductMachine
noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev Input := FixedGadgetSubstitution.Compiler.Input s b arity × List Bool
abbrev Output := FixedGadgetSubstitution.Compiler.Input
  (Catalogue.vertexCount (s := s) (arity := arity)) (Catalogue.edgeCount (b := b))
  (Catalogue.targetArity (s := s) (arity := arity))

def raw (x : Input (s := s) (b := b) (arity := arity)) : RawClosedNetwork where
  vertices := x.1.val.vertices.map (fun row => Records.vertex (s := s) (arity := arity) (x.2, row))
  edges := List.ofFn (fun e : Fin x.1.val.edges.length => Records.edge (b := b) (x.2, x.1.val.edges.get e, e.val))

@[simp] theorem vertices_length (x : Input (s := s) (b := b) (arity := arity)) :
    (raw x).vertices.length = x.1.val.vertices.length := by simp [raw]
@[simp] theorem edges_length (x : Input (s := s) (b := b) (arity := arity)) :
    (raw x).edges.length = x.1.val.edges.length := by simp [raw]

def vertexIndex (x : Input (s := s) (b := b) (arity := arity)) :
    Fin x.1.val.vertices.length ≃ Fin (raw x).vertices.length := finCongr (vertices_length x).symm
def edgeIndex (x : Input (s := s) (b := b) (arity := arity)) :
    Fin x.1.val.edges.length ≃ Fin (raw x).edges.length := finCongr (edges_length x).symm

theorem vertex_get (x : Input (s := s) (b := b) (arity := arity)) (v : Fin x.1.val.vertices.length) :
    (raw x).vertices.get (vertexIndex x v) = Records.vertex (s := s) (arity := arity) (x.2, x.1.val.vertices.get v) := by
  simp [raw, vertexIndex, finCongr, List.get_eq_getElem]
  rfl
theorem edge_get (x : Input (s := s) (b := b) (arity := arity)) (e : Fin x.1.val.edges.length) :
    (raw x).edges.get (edgeIndex x e) = Records.edge (b := b) (x.2, x.1.val.edges.get e, e.val) := by
  simp [raw, edgeIndex, finCongr, List.get_eq_getElem]
  rfl

theorem vertex_ports (x : Input (s := s) (b := b) (arity := arity)) (v : Fin x.1.val.vertices.length) :
    ((raw x).vertices.get (vertexIndex x v)).2 = (x.1.val.vertices.get v).2 := by
  rw [vertex_get]; rfl

theorem endpoints (x : Input (s := s) (b := b) (arity := arity)) :
    (raw x).endpoints = x.1.val.endpoints := by
  simp [raw, RawClosedNetwork.endpoints, Records.vertex, List.map_map, Function.comp_def]

theorem vertex_range_arity (x : Input (s := s) (b := b) (arity := arity)) (v : Fin x.1.val.vertices.length) :
    ((raw x).vertices.get (vertexIndex x v)).1 < Catalogue.vertexCount (s := s) (arity := arity) ∧
      Catalogue.targetArity (s := s) (arity := arity) ((raw x).vertices.get (vertexIndex x v)).1 =
        arity (x.1.val.vertices.get v).1 := by
  rw [vertex_get]
  change Records.vertexLabel (s := s) (arity := arity) (x.2, x.1.val.vertices.get v) < _ ∧
    Catalogue.targetArity (s := s) (arity := arity)
      (Records.vertexLabel (s := s) (arity := arity) (x.2, x.1.val.vertices.get v)) = _
  rw [Records.vertex_label _ (x.1.property.1 v).1]
  exact ⟨(Catalogue.vertexEquiv _).isLt, Catalogue.arity_code _⟩

theorem wellFormed (x : Input (s := s) (b := b) (arity := arity)) :
    (raw x).WellFormed (Catalogue.vertexCount (s := s) (arity := arity))
      (Catalogue.edgeCount (b := b)) (Catalogue.targetArity (s := s) (arity := arity)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    obtain ⟨v, rfl⟩ := (vertexIndex x).surjective v
    refine ⟨(vertex_range_arity x v).1, ?_⟩
    rw [vertex_ports, (vertex_range_arity x v).2]
    exact (x.1.property.1 v).2
  · intro e
    obtain ⟨e, rfl⟩ := (edgeIndex x).surjective e
    rw [edge_get, Records.edge_label _ (x.1.property.2.1 e)]
    exact (Catalogue.edgeEquiv _).isLt
  · rw [endpoints]
    have he : (raw x).expectedEndpoints = x.1.val.expectedEndpoints := by
      simp only [RawClosedNetwork.expectedEndpoints, edges_length]
      rfl
    rw [he]
    exact x.1.property.2.2

def value (x : Input (s := s) (b := b) (arity := arity)) : Output (s := s) (b := b) (arity := arity) :=
  ⟨raw x, wellFormed x⟩

def reference (x : Input (s := s) (b := b) (arity := arity)) : (Fin x.1.val.edges.length × Bool) → Bool :=
  fun e => x.2.getD (Endpoint.number (e.1.val, e.2)) false

/-- A correctly sized supplied word is read literally, in 2*edge+bit order. -/
theorem reference_ofFn (r : FixedGadgetSubstitution.Compiler.Input s b arity)
    (w : Word (2 * r.val.edges.length)) (e : Fin r.val.edges.length × Bool) :
    reference (r, List.ofFn w) e = w (Endpoint.typed r.val.edges.length e) :=
  AffineMachine.DensePrograms.getD_ofFn w (Endpoint.typed r.val.edges.length e) false

theorem reference_outside (x : Input (s := s) (b := b) (arity := arity))
    (e : Fin x.1.val.edges.length × Bool) (h : x.2.length ≤ Endpoint.number (e.1.val, e.2)) :
    reference x e = false := List.getD_eq_default x.2 false h

end
end Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Graph
