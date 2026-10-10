import Holant.Proofs.Algorithms.TransformRecognition.RationalSparseMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalMatrixMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev bitsEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev inputEncoding := pairEncoding encodingNatBool bitsEncoding

def matrix (n : ℕ) (a b : Bool) : RationalSparseMachine.Poly :=
  RationalSparseMachine.variable n (SymbolicTransform.index a b).val
def cofactor (n : ℕ) (a b : Bool) : RationalSparseMachine.Poly :=
  if a=b then matrix n (!a) (!b) else RationalSparseMachine.neg (matrix n a b)
def inverse (n : ℕ) (a b : Bool) : RationalSparseMachine.Poly :=
  RationalSparseMachine.mul (RationalSparseMachine.variable n 4) (cofactor n a b)
def guard (n : ℕ) : RationalSparseMachine.Poly :=
  RationalSparseMachine.sub (RationalSparseMachine.mul (RationalSparseMachine.variable n 4)
    (RationalSparseMachine.sub (RationalSparseMachine.mul (matrix n false false) (matrix n true true))
      (RationalSparseMachine.mul (matrix n false true) (matrix n true false)))) (RationalSparseMachine.one n)

theorem matrix_wire (q : ℕ) (a b : Bool) :
    matrix (5+q) a b = RationalInputMachine.rowWire
      (SparseTransform.matrix RationalCompiler.data q a b) :=
  RationalSparseMachine.variable_wire (Fin.castAdd q (SymbolicTransform.index a b))

theorem inverse_wire (q : ℕ) (a b : Bool) :
    inverse (5+q) a b = RationalInputMachine.rowWire
      (SparseTransform.inverse RationalCompiler.data q a b) := by
  have h4 : RationalSparseMachine.variable (5+q) 4 = RationalInputMachine.rowWire
      (SparseTransform.variableCode RationalCompiler.data (Fin.castAdd q (4 : Fin 5))) :=
    RationalSparseMachine.variable_wire (Fin.castAdd q (4 : Fin 5))
  by_cases h : a=b
  · simp only [inverse,cofactor,h,ite_true,SparseTransform.inverse]
    rw [h4,matrix_wire,RationalSparseMachine.mul_wire]
  · simp only [inverse,cofactor,h,ite_false,SparseTransform.inverse]
    rw [h4,matrix_wire,RationalSparseMachine.neg_wire,RationalSparseMachine.mul_wire]

theorem guard_wire (q : ℕ) :
    guard (5+q) = RationalInputMachine.rowWire
      (SparseTransform.guard RationalCompiler.data q) := by
  unfold guard SparseTransform.guard
  have h4 : RationalSparseMachine.variable (5+q) 4 = RationalInputMachine.rowWire
      (SparseTransform.variableCode RationalCompiler.data (Fin.castAdd q (4 : Fin 5))) :=
    RationalSparseMachine.variable_wire (Fin.castAdd q (4 : Fin 5))
  rw [h4]
  simp only [matrix_wire,RationalSparseMachine.mul_wire,RationalSparseMachine.sub_wire,RationalSparseMachine.one_wire]

noncomputable section

def indexComputes : Computes bitsEncoding encodingNatBool
    (fun p : Bool × Bool => (SymbolicTransform.index p.1 p.2).val) :=
  GraphPreprocessing.FiniteRecode.computes bitsEncoding encodingNatBool _ 64
    (fun ⟨a,b⟩ => by cases a <;> cases b <;> decide)

def cofactorIndex : Bool × Bool → ℕ := fun p =>
  if p.1=p.2 then (SymbolicTransform.index (!p.1) (!p.2)).val
  else (SymbolicTransform.index p.1 p.2).val
def cofactorIndexComputes : Computes bitsEncoding encodingNatBool cofactorIndex :=
  GraphPreprocessing.FiniteRecode.computes bitsEncoding encodingNatBool _ 64
    (fun ⟨a,b⟩ => by cases a <;> cases b <;> decide)
def diagonalComputes : Computes bitsEncoding encodingBoolBool
    (fun p : Bool × Bool => decide (p.1=p.2)) :=
  equalComputes encodingBoolBool

def matrixExecutes : Executes inputEncoding RationalSparseMachine.encoding
    (fun p : ℕ × (Bool × Bool) => matrix p.1 p.2.1 p.2.2) :=
  (Executes.ofComputes (pairComputes
    (Wiring.firstComputes encodingNatBool bitsEncoding)
    ((Wiring.secondComputes encodingNatBool bitsEncoding).andThen indexComputes))).comp
      RationalSparseMachine.variableExecutes

/-- The branch only selects/negates an already generated polynomial. Its
arbitrarily long term list is processed by the list machine, not finite recode. -/
def signComputes : Computes (pairEncoding encodingBoolBool RationalSparseMachine.encoding) RationalSparseMachine.encoding
    (fun p : Bool × RationalSparseMachine.Poly => if p.1 then p.2 else RationalSparseMachine.neg p.2) :=
  ifComputes (Wiring.firstComputes encodingBoolBool RationalSparseMachine.encoding)
    (Wiring.secondComputes encodingBoolBool RationalSparseMachine.encoding)
    ((Wiring.secondComputes encodingBoolBool RationalSparseMachine.encoding).andThen RationalSparseMachine.negComputes)

def cofactorExecutes : Executes inputEncoding RationalSparseMachine.encoding
    (fun p : ℕ × (Bool × Bool) => cofactor p.1 p.2.1 p.2.2) := by
  let bits := Wiring.secondComputes encodingNatBool bitsEncoding
  let entry :=  (Executes.ofComputes (pairComputes
    (Wiring.firstComputes encodingNatBool bitsEncoding)
    (bits.andThen cofactorIndexComputes))).comp RationalSparseMachine.variableExecutes
  refine (((Executes.ofComputes (bits.andThen diagonalComputes)).pair entry).comp
    (Executes.ofComputes signComputes)).congr ?_
  intro p
  by_cases h : p.2.1=p.2.2 <;> simp [cofactorIndex,cofactor,matrix,h]

def inverseExecutes : Executes inputEncoding RationalSparseMachine.encoding
    (fun p : ℕ × (Bool × Bool) => inverse p.1 p.2.1 p.2.2) := by
  let detInv := (Executes.ofComputes (pairComputes
    (Wiring.firstComputes encodingNatBool bitsEncoding)
    (constantComputes inputEncoding encodingNatBool 4))).comp RationalSparseMachine.variableExecutes
  exact (detInv.pair cofactorExecutes).comp RationalSparseMachine.mulExecutes

def matrixAt (a b : Bool) : Executes encodingNatBool RationalSparseMachine.encoding
    (fun n => matrix n a b) :=
  (Executes.ofComputes (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool bitsEncoding (a,b)))).comp matrixExecutes

def guardExecutes : Executes encodingNatBool RationalSparseMachine.encoding guard := by
  let diagonal := ((matrixAt false false).pair (matrixAt true true)).comp RationalSparseMachine.mulExecutes
  let offDiagonal := ((matrixAt false true).pair (matrixAt true false)).comp RationalSparseMachine.mulExecutes
  let determinant := (diagonal.pair offDiagonal).comp (Executes.ofComputes RationalSparseMachine.subComputes)
  let detInv := (Executes.ofComputes (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool encodingNatBool 4))).comp RationalSparseMachine.variableExecutes
  let lhs := (detInv.pair determinant).comp RationalSparseMachine.mulExecutes
  exact (lhs.pair RationalSparseMachine.oneExecutes).comp (Executes.ofComputes RationalSparseMachine.subComputes)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalMatrixMachine
