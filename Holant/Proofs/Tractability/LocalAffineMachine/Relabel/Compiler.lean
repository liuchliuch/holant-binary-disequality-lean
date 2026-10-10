import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.Graph


namespace Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Compiler

open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler AffineMachine UniversalPairReduction.SmoothingCompiler
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ}

def inputEncoding := pairEncoding (RawClosedNetwork.validatedEncoding s b arity) WordLookup.wordEncoding
def outputEncoding := RawClosedNetwork.validatedEncoding (Catalogue.vertexCount (s := s) (arity := arity))
  (Catalogue.edgeCount (b := b)) (Catalogue.targetArity (s := s) (arity := arity))

def source : Computes (inputEncoding (s := s) (b := b) (arity := arity))
    (RawClosedNetwork.validatedEncoding s b arity) Prod.fst := Wiring.firstComputes _ _
def word : Computes (inputEncoding (s := s) (b := b) (arity := arity)) WordLookup.wordEncoding Prod.snd :=
  Wiring.secondComputes _ _

def verticesComputes : Computes (inputEncoding (s := s) (b := b) (arity := arity))
    (framedListEncoding RawClosedNetwork.vertexEncoding) (fun x => (Graph.raw x).vertices) :=
  (pairComputes word (source.andThen (rowsComputes s b arity))).andThen
    (mapListComputes WordLookup.wordEncoding RawClosedNetwork.vertexEncoding RawClosedNetwork.vertexEncoding
      (fun w r => Records.vertex (s := s) (arity := arity) (w, r)) Records.vertexComputes)

def edgeCellComputes :
    Computes (pairEncoding (inputEncoding (s := s) (b := b) (arity := arity)) UnaryBinary.unaryEncoding)
      encodingNatBool
      (fun x => Records.edge (b := b) (x.1.2, x.1.1.val.edges.getD x.2 0, x.2)) := by
  let context := Wiring.firstComputes (inputEncoding (s := s) (b := b) (arity := arity)) UnaryBinary.unaryEncoding
  let index := Wiring.secondComputes (inputEncoding (s := s) (b := b) (arity := arity)) UnaryBinary.unaryEncoding
  let labels := (context.andThen source).andThen (FixedGadgetSubstitution.Compiler.edgesComputes s b arity)
  let label := AccessPrograms.get encodingNatBool 0 labels index
  exact (pairComputes (context.andThen word) (pairComputes label (index.andThen UnaryBinary.computes))).andThen
    Records.edgeComputes

def edgesComputes : Computes (inputEncoding (s := s) (b := b) (arity := arity))
    (framedListEncoding encodingNatBool) (fun x => (Graph.raw x).edges) := by
  let rows := WireLists.tabulate (inputEncoding (s := s) (b := b) (arity := arity)) encodingNatBool (fun x => x.1.val.edges.length)
    (source.andThen (edgeCountComputes s b arity))
    (fun x i => Records.edge (b := b) (x.2, x.1.val.edges.getD i 0, i)) edgeCellComputes
  refine congrComputes rows ?_
  intro x
  rw [DensePrograms.range_map]
  congr 1; funext e
  rw [List.getD_eq_getElem _ _ e.isLt]
  rfl

def computes : Computes (inputEncoding (s := s) (b := b) (arity := arity)) outputEncoding Graph.value :=
  recode (pairComputes verticesComputes edgesComputes) id (fun _ => rfl) (fun _ => rfl)

theorem input_length (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    (inputEncoding.encode x).length =
      2 * (RawClosedNetwork.encoding.encode x.1.val).length + 4 * x.2.length + 2 := by
  simp [inputEncoding, pairEncoding_length, WordLookup.word_length, RawClosedNetwork.validatedEncoding]
  omega

def outputPolynomial : Polynomial ℕ := (computes (s := s) (b := b) (arity := arity)).outputBound.bound

theorem output_bits (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    (RawClosedNetwork.encoding.encode (Graph.raw x)).length ≤
      (outputPolynomial (s := s) (b := b) (arity := arity)).eval (inputEncoding.encode x).length :=
  (computes (s := s) (b := b) (arity := arity)).outputBound.length_le x

theorem primitive_bound (x : Graph.Input (s := s) (b := b) (arity := arity)) :
    let w := computes (s := s) (b := b) (arity := arity)
    primitiveCost w.machine (w.outputs x).steps
      (some (initList w.machine.computer (inputEncoding.encode x))) ≤
        (primitivePolynomial w).eval (inputEncoding.encode x).length :=
  computes_primitive_cost (computes (s := s) (b := b) (arity := arity)) x

end
end Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Compiler
