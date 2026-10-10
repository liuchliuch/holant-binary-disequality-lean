import Holant.Proofs.Tractability.EOEvaluation.CandidateExecution.Records


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Graph
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing AffineMachine LocalAffineMachine.Relabel FixedGadgetSubstitution.Compiler
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
abbrev Input := Responses.Input (s := s) (arity := arity)
abbrev Output := FixedGadgetSubstitution.Compiler.Input
  (Catalogue.count (s := s) (arity := arity)) 1 (Catalogue.targetArity (s := s) (arity := arity))
def outputEncoding := RawClosedNetwork.validatedEncoding (Catalogue.count (s := s) (arity := arity)) 1
  (Catalogue.targetArity (s := s) (arity := arity))

def raw (x : Input (s := s) (arity := arity)) : RawClosedNetwork where
  vertices := List.ofFn (fun v : Fin x.1.val.vertices.length => Records.vertex (x, v.val, x.1.val.vertices.get v))
  edges := x.1.val.edges
@[simp] theorem vertices_length (x : Input (s := s) (arity := arity)) :
    (raw x).vertices.length = x.1.val.vertices.length := by simp [raw]
def vertexIndex (x : Input (s := s) (arity := arity)) :
    Fin x.1.val.vertices.length ≃ Fin (raw x).vertices.length := finCongr (vertices_length x).symm
theorem vertex_get (x : Input (s := s) (arity := arity)) (v : Fin x.1.val.vertices.length) :
    (raw x).vertices.get (vertexIndex x v) = Records.vertex (x, v.val, x.1.val.vertices.get v) := by
  simp [raw, vertexIndex, List.get_eq_getElem]
theorem vertex_arity (x : Input (s := s) (arity := arity)) (v : Fin x.1.val.vertices.length) :
    Catalogue.targetArity (s := s) (arity := arity) ((raw x).vertices.get (vertexIndex x v)).1 =
      arity (x.1.val.vertices.get v).1 := by
  rw [vertex_get]
  change Catalogue.targetArity (s := s) (arity := arity)
    (Records.label (x, v.val, x.1.val.vertices.get v)) = _
  rw [Records.label_valid (x, v.val, x.1.val.vertices.get v) (x.1.property.1 v).1]
  exact Catalogue.arity_code _
theorem endpoints (x : Input (s := s) (arity := arity)) : (raw x).endpoints = x.1.val.endpoints := by
  simp only [raw, RawClosedNetwork.endpoints, List.map_ofFn, Records.vertex]
  change (List.ofFn (fun v : Fin x.1.val.vertices.length =>
    (x.1.val.vertices[v.val]).2)).flatten = (x.1.val.vertices.map Prod.snd).flatten
  rw [List.ofFn_getElem_eq_map]

theorem wellFormed (x : Input (s := s) (arity := arity)) :
    (raw x).WellFormed (Catalogue.count (s := s) (arity := arity)) 1 (Catalogue.targetArity (s := s) (arity := arity)) := by
  refine ⟨?_, x.1.property.2.1, ?_⟩
  · intro v
    obtain ⟨v, rfl⟩ := (vertexIndex x).surjective v
    constructor
    · rw [vertex_get]
      change Records.label (x, v.val, x.1.val.vertices.get v) < _
      rw [Records.label_valid (x, v.val, x.1.val.vertices.get v) (x.1.property.1 v).1]
      exact (Catalogue.codes (Records.candidate (x, v.val, x.1.val.vertices.get v)
        ⟨(x.1.val.vertices.get v).1, (x.1.property.1 v).1⟩)).isLt
    · rw [vertex_arity, vertex_get]
      exact (x.1.property.1 v).2
  · rw [endpoints]
    exact x.1.property.2.2
def value (x : Input (s := s) (arity := arity)) : Output (s := s) (arity := arity) := ⟨raw x, wellFormed x⟩

def cellComputes : Computes (pairEncoding (Responses.inputEncoding (s := s) (arity := arity)) UnaryBinary.unaryEncoding)
    RawClosedNetwork.vertexEncoding (fun x => Records.vertex (x.1, x.2, x.1.1.val.vertices.getD x.2 (0, []))) := by
  let ctx := Wiring.firstComputes (Responses.inputEncoding (s := s) (arity := arity))
    UnaryBinary.unaryEncoding
  let v := Wiring.secondComputes (Responses.inputEncoding (s := s) (arity := arity))
    UnaryBinary.unaryEncoding
  let row := AccessPrograms.get RawClosedNetwork.vertexEncoding (0, [])
    (ctx.andThen ((Responses.source (s := s) (arity := arity)).andThen (rowsComputes s 1 arity))) v
  exact (pairComputes ctx (pairComputes v row)).andThen
    (Records.computes (s := s) (arity := arity))
def verticesComputes : Computes (Responses.inputEncoding (s := s) (arity := arity))
    (framedListEncoding RawClosedNetwork.vertexEncoding) (fun x => (raw x).vertices) := by
  refine congrComputes (WireLists.tabulate (Responses.inputEncoding (s := s) (arity := arity))
    RawClosedNetwork.vertexEncoding (fun x => x.1.val.vertices.length)
    ((Responses.source (s := s) (arity := arity)).andThen (vertexCountComputes s 1 arity))
    (fun x v => Records.vertex (x, v, x.1.val.vertices.getD v (0, [])))
    (cellComputes (s := s) (arity := arity))) ?_
  intro x
  rw [DensePrograms.range_map]
  simp [raw, List.getD_eq_getElem]
def computes : Computes (Responses.inputEncoding (s := s) (arity := arity))
    (outputEncoding (s := s) (arity := arity)) (value (s := s) (arity := arity)) :=
  recode (pairComputes (verticesComputes (s := s) (arity := arity))
    ((Responses.source (s := s) (arity := arity)).andThen (edgesComputes s 1 arity))) id
    (fun _ => rfl) (fun _ => rfl)

/-- The flag is physically computed; wrong response lengths are not endorsed.
The graph remains a total, well-formed intermediate value on every list. -/
def checkedComputes : Computes (Responses.inputEncoding (s := s) (arity := arity))
    (pairEncoding encodingBoolBool (outputEncoding (s := s) (arity := arity)))
    (fun x => (Responses.valid x, value x)) :=
  pairComputes (Responses.validComputes (s := s) (arity := arity))
    (computes (s := s) (arity := arity))

theorem primitive_bound (x : Input (s := s) (arity := arity)) :
    primitiveCost (computes (s := s) (arity := arity)).machine
      ((computes (s := s) (arity := arity)).outputs x).steps
      (some (Turing.initList (computes (s := s) (arity := arity)).machine.computer
        ((Responses.inputEncoding (s := s) (arity := arity)).encode x))) ≤
        (primitivePolynomial (computes (s := s) (arity := arity))).eval
          ((Responses.inputEncoding (s := s) (arity := arity)).encode x).length :=
  computes_primitive_cost (computes (s := s) (arity := arity)) x

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Graph
