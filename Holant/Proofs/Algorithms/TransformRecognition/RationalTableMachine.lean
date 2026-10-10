import Holant.Proofs.Algorithms.TransformRecognition.RationalEdgeMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalTableMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Word := RationalTensorMachine.Word
abbrev Input := ℕ × (ℕ × List RationalTensorMachine.Row)
abbrev Entry := Word × RationalSparseMachine.Poly
abbrev wordEncoding := RationalTensorMachine.wordEncoding
abbrev tailEncoding := pairEncoding encodingNatBool RationalTensorMachine.tableEncoding
abbrev encoding := pairEncoding encodingNatBool tailEncoding
abbrev entryEncoding := pairEncoding wordEncoding RationalSparseMachine.encoding
abbrev outputEncoding := framedListEncoding entryEncoding

def words (n : ℕ) : List Word := StructuralListMachine.exactLength [false,true] n
def entry (r : Input) (x : Word) : Entry :=
  (x,RationalTensorMachine.vertex (r.1,x,r.2.2))
def table (r : Input) : List Entry := (words r.2.1).map (entry r)

theorem vectors_eq (n : ℕ) :
    FiniteBranchEnumeration.vectors [false,true] n = SparseTransform.allWords n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FiniteBranchEnumeration.vectors,SparseTransform.allWords,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,ih]

theorem words_eq (n : ℕ) : words n = (SparseTransform.allWords n).map List.ofFn := by
  rw [words,StructuralListMachine.exactLength,vectors_eq]

theorem table_wire {n q : ℕ} (address : (Fin n → Bool) → Fin (5+q)) :
    table (5+q,n,(SparseTransform.allWords n).map (fun y => RationalTensorMachine.wireRow (y,address y))) =
      (SparseTransform.allWords n).map (fun x =>
        (List.ofFn x,RationalInputMachine.rowWire (SymbolicInputTable.vertex RationalCompiler.data
          (SparseTransform.inverse RationalCompiler.data q)
          (fun y => SparseTransform.variableCode RationalCompiler.data (address y)) x))) := by
  simp only [table,words_eq,List.map_map,Function.comp_def,entry,
    RationalTensorMachine.dense_vertex_wire]

theorem words_zero : words 0 = [[]] := rfl
theorem table_length (r : Input) : (table r).length = 2^r.2.1 := by
  simp only [table,words_eq,List.length_map,SparseTransform.allWords_length]

noncomputable section

def wordsExecutes : Executes encodingNatBool (framedListEncoding wordEncoding) words :=
  (Executes.ofComputes (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool wordEncoding [false,true]))).comp
      (StructuralListMachine.exactExecutes encodingBoolBool)

def entryExecutes : Executes (pairEncoding encoding wordEncoding) entryEncoding
    (fun p : Input × Word => entry p.1 p.2) := by
  let r := Wiring.firstComputes encoding wordEncoding
  let x := Wiring.secondComputes encoding wordEncoding
  let width := r.andThen (Wiring.firstComputes encodingNatBool tailEncoding)
  let tail := r.andThen (Wiring.secondComputes encodingNatBool tailEncoding)
  let source := tail.andThen (Wiring.secondComputes encodingNatBool RationalTensorMachine.tableEncoding)
  let prepare := pairComputes width (pairComputes x source)
  exact (Executes.ofComputes x).pair
    ((Executes.ofComputes prepare).comp RationalTensorMachine.vertexExecutes)

def executes : Executes encoding outputEncoding table := by
  let arity := (Wiring.secondComputes encodingNatBool tailEncoding).andThen
    (Wiring.firstComputes encodingNatBool RationalTensorMachine.tableEncoding)
  exact NegativeCertificateMachine.Lists.map encoding wordEncoding entryEncoding
    ((Executes.ofComputes arity).comp wordsExecutes) entry entryExecutes

def source_outputs {n q : ℕ} (address : (Fin n → Bool) → Fin (5+q)) :
    TM2OutputsInTime executes.machine.computer
      (encoding.encode (5+q,n,(SparseTransform.allWords n).map
        (fun y => RationalTensorMachine.wireRow (y,address y))))
      (some (outputEncoding.encode ((SparseTransform.allWords n).map (fun x =>
        (List.ofFn x,RationalInputMachine.rowWire (SymbolicInputTable.vertex RationalCompiler.data
          (SparseTransform.inverse RationalCompiler.data q)
          (fun y => SparseTransform.variableCode RationalCompiler.data (address y)) x))))))
      (executes.cost (5+q,n,(SparseTransform.allWords n).map
        (fun y => RationalTensorMachine.wireRow (y,address y)))) := by
  have h := executes.outputs (5+q,n,(SparseTransform.allWords n).map
    (fun y => RationalTensorMachine.wireRow (y,address y)))
  rw [table_wire] at h
  exact h

theorem primitive_bound (r : Input) :
    primitiveCost executes.machine (executes.outputs r).steps
      (some (initList executes.machine.computer (encoding.encode r))) ≤
        executes.cost r * executes.machine.primitiveBudget := executes.primitive_bound r

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalTableMachine
