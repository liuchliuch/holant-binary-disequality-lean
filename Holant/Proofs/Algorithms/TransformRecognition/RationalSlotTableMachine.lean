import Holant.Proofs.Algorithms.TransformRecognition.RationalTableMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalSlotTableMachine
set_option backward.isDefEq.respectTransparency false
open Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Input := Bool × RationalTableMachine.Input
abbrev encoding := pairEncoding encodingBoolBool RationalTableMachine.encoding
abbrev cellEncoding := pairEncoding encoding RationalTensorMachine.wordEncoding

def polynomial (r : Input) (x : RationalTensorMachine.Word) : RationalSparseMachine.Poly :=
  if r.1 then RationalEdgeMachine.edge (r.2.1,(x.getD 0 false,x.getD 1 false),r.2.2.2.map Prod.snd)
  else RationalTensorMachine.vertex (r.2.1,x,r.2.2.2)
def table (r : Input) : List RationalTableMachine.Entry :=
  (RationalTableMachine.words r.2.2.1).map (fun x => (x,polynomial r x))

noncomputable section
def flag := Wiring.firstComputes encodingBoolBool RationalTableMachine.encoding
def input := Wiring.secondComputes encodingBoolBool RationalTableMachine.encoding
def width := input.andThen (Wiring.firstComputes encodingNatBool RationalTableMachine.tailEncoding)
def tail := input.andThen (Wiring.secondComputes encodingNatBool RationalTableMachine.tailEncoding)
def arity := tail.andThen (Wiring.firstComputes encodingNatBool RationalTensorMachine.tableEncoding)
def sourceTable := tail.andThen (Wiring.secondComputes encodingNatBool RationalTensorMachine.tableEncoding)
def edgeAddresses := sourceTable.andThen
  (WireLists.mapComputes RationalTensorMachine.rowEncoding encodingNatBool Prod.snd
    (Wiring.secondComputes RationalTensorMachine.wordEncoding encodingNatBool))

def polynomialExecutes : Executes cellEncoding RationalSparseMachine.encoding
    (fun p : Input × RationalTensorMachine.Word => polynomial p.1 p.2) := by
  let ctx := Wiring.firstComputes encoding RationalTensorMachine.wordEncoding
  let x := Wiring.secondComputes encoding RationalTensorMachine.wordEncoding
  let vertex := (Executes.ofComputes (pairComputes (ctx.andThen width)
    (pairComputes x (ctx.andThen sourceTable)))).comp RationalTensorMachine.vertexExecutes
  let bit (j : ℕ) := AccessPrograms.get encodingBoolBool false x
    (constantComputes cellEncoding GraphPreprocessing.UnaryBinary.unaryEncoding j)
  let edge := (Executes.ofComputes (pairComputes (ctx.andThen width)
    (pairComputes (pairComputes (bit 0) (bit 1)) (ctx.andThen edgeAddresses)))).comp RationalEdgeMachine.edgeExecutes
  let choose := ifComputes (Wiring.firstComputes encodingBoolBool RationalSparseMachine.pairEncoding)
    ((Wiring.secondComputes encodingBoolBool RationalSparseMachine.pairEncoding).andThen
      (Wiring.firstComputes RationalSparseMachine.encoding RationalSparseMachine.encoding))
    ((Wiring.secondComputes encodingBoolBool RationalSparseMachine.pairEncoding).andThen
      (Wiring.secondComputes RationalSparseMachine.encoding RationalSparseMachine.encoding))
  exact ((Executes.ofComputes (ctx.andThen flag)).pair (edge.pair vertex)).comp (Executes.ofComputes choose)

def executes : Executes encoding RationalTableMachine.outputEncoding table :=
  NegativeCertificateMachine.Lists.map encoding RationalTensorMachine.wordEncoding RationalTableMachine.entryEncoding
    ((Executes.ofComputes arity).comp RationalTableMachine.wordsExecutes)
    (fun r x => (x,polynomial r x))
    ((Executes.ofComputes (Wiring.secondComputes encoding RationalTensorMachine.wordEncoding)).pair polynomialExecutes)
end

theorem vertex_polynomial {n q : ℕ} (address : (Fin n → Bool) → Fin (5+q)) (x : Fin n → Bool) :
    polynomial (false,5+q,n,(SparseTransform.allWords n).map
      (fun y => RationalTensorMachine.wireRow (y,address y))) (List.ofFn x) =
      RationalInputMachine.rowWire (SymbolicInputTable.vertex RationalCompiler.data
        (SparseTransform.inverse RationalCompiler.data q)
        (fun y => SparseTransform.variableCode RationalCompiler.data (address y)) x) :=
  RationalTensorMachine.dense_vertex_wire x address

end Holant.LocalDrafts.MainChain.TransformRecognition.RationalSlotTableMachine
