import Holant.Proofs.Algorithms.TransformRecognition.RationalTensorMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalEdgeMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev Input := ℕ × ((Bool × Bool) × List ℕ)
abbrev addressesEncoding := framedListEncoding encodingNatBool
abbrev bitsEncoding := RationalMatrixMachine.bitsEncoding
abbrev tailEncoding := pairEncoding bitsEncoding addressesEncoding
abbrev encoding := pairEncoding encodingNatBool tailEncoding

def address (r : Input) (i j : Bool) : ℕ :=
  r.2.2.getD (SymbolicTransform.index i j).val 0

def term (r : Input) (i j : Bool) : RationalSparseMachine.Poly :=
  RationalSparseMachine.mul
    (RationalSparseMachine.mul (RationalMatrixMachine.matrix r.1 i r.2.1.1)
      (RationalSparseMachine.variable r.1 (address r i j)))
    (RationalMatrixMachine.matrix r.1 j r.2.1.2)

def edge (r : Input) : RationalSparseMachine.Poly :=
  [false,true].flatMap (fun i => [false,true].flatMap (fun j => term r i j))

theorem term_wire {q : ℕ} (a b i j : Bool) (addresses : List ℕ)
    (E : Bool → Bool → Fin (5+q))
    (h : addresses.getD (SymbolicTransform.index i j).val 0 = (E i j).val) :
    term (5+q,(a,b),addresses) i j = RationalInputMachine.rowWire
      (Sparse.mul RationalCompiler.data
        (Sparse.mul RationalCompiler.data (SparseTransform.matrix RationalCompiler.data q i a)
          (SparseTransform.variableCode RationalCompiler.data (E i j)))
        (SparseTransform.matrix RationalCompiler.data q j b)) := by
  unfold term address
  rw [h,RationalMatrixMachine.matrix_wire,RationalMatrixMachine.matrix_wire,
    RationalSparseMachine.variable_wire,RationalSparseMachine.mul_wire,RationalSparseMachine.mul_wire]

theorem edge_wire {q : ℕ} (a b : Bool) (addresses : List ℕ)
    (E : Bool → Bool → Fin (5+q))
    (h : ∀ i j, addresses.getD (SymbolicTransform.index i j).val 0 = (E i j).val) :
    edge (5+q,(a,b),addresses) = RationalInputMachine.rowWire
      (SymbolicInputTable.edge RationalCompiler.data
        (SparseTransform.matrix RationalCompiler.data q)
        (fun i j => SparseTransform.variableCode RationalCompiler.data (E i j)) a b) := by
  simp only [edge,SymbolicInputTable.edge,SparseTransform.total,List.flatMap_cons,
    List.flatMap_nil,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [term_wire a b false false addresses E (h false false),
    term_wire a b false true addresses E (h false true),
    term_wire a b true false addresses E (h true false),
    term_wire a b true true addresses E (h true true)]
  simp only [RationalInputMachine.rowWire,List.flatten_append,List.flatten_cons,
    List.flatten_nil,List.append_nil,List.map_append,List.append_assoc]

noncomputable section

def width : Computes encoding encodingNatBool (fun r : Input => r.1) :=
  Wiring.firstComputes encodingNatBool tailEncoding
def tail : Computes encoding tailEncoding (fun r : Input => r.2) :=
  Wiring.secondComputes encodingNatBool tailEncoding
def bits : Computes encoding bitsEncoding (fun r : Input => r.2.1) :=
  tail.andThen (Wiring.firstComputes bitsEncoding addressesEncoding)
def addresses : Computes encoding addressesEncoding (fun r : Input => r.2.2) :=
  tail.andThen (Wiring.secondComputes bitsEncoding addressesEncoding)

def matrixLeft (i : Bool) : Executes encoding RationalSparseMachine.encoding
    (fun r : Input => RationalMatrixMachine.matrix r.1 i r.2.1.1) :=
  (Executes.ofComputes (pairComputes width (pairComputes
    (constantComputes encoding encodingBoolBool i)
    (bits.andThen (Wiring.firstComputes encodingBoolBool encodingBoolBool))))).comp
      RationalMatrixMachine.matrixExecutes

def matrixRight (j : Bool) : Executes encoding RationalSparseMachine.encoding
    (fun r : Input => RationalMatrixMachine.matrix r.1 j r.2.1.2) :=
  (Executes.ofComputes (pairComputes width (pairComputes
    (constantComputes encoding encodingBoolBool j)
    (bits.andThen (Wiring.secondComputes encodingBoolBool encodingBoolBool))))).comp
      RationalMatrixMachine.matrixExecutes

def termExecutes (i j : Bool) : Executes encoding RationalSparseMachine.encoding
    (fun r => term r i j) := by
  let index := constantComputes encoding encodingNatBool (SymbolicTransform.index i j).val
  let coefficientAddress := (Executes.ofComputes (pairComputes addresses index)).comp
    (NegativeCertificateMachine.Lists.lookup encodingNatBool 0)
  let coefficient := ((Executes.ofComputes width).pair coefficientAddress).comp
    RationalSparseMachine.variableExecutes
  let left := ((matrixLeft i).pair coefficient).comp RationalSparseMachine.mulExecutes
  exact (left.pair (matrixRight j)).comp RationalSparseMachine.mulExecutes

def edgeExecutes : Executes encoding RationalSparseMachine.encoding edge := by
  let concat {f g : Input → RationalSparseMachine.Poly}
      (u : Executes encoding RationalSparseMachine.encoding f)
      (v : Executes encoding RationalSparseMachine.encoding g) :=
    (u.pair v).comp (Executes.ofComputes RationalSparseMachine.addComputes)
  exact (concat (concat (termExecutes false false) (termExecutes false true))
    (concat (termExecutes true false) (termExecutes true true))).congr
      (fun r => by simp only [edge,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc])

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalEdgeMachine
