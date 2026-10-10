import Holant.Proofs.Algorithms.TransformRecognition.RationalMatrixMachine
import Holant.Proofs.Algorithms.TransformRecognition.SparseEvaluation
import Holant.Tractable.KPresentation

/-! Runtime sparse constraints for the internally prescribed identity/K/KX
basis. Root binding positions and total width are data produced by the original
allocator. No matrix values or transformed RootCodes are accepted as answers.
This compiler component still requires its original-root assembler and semantic
basis specialization before it is a criterion recognizer. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorBasis
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open CommonFieldMachine (Executes)

abbrev Layout := ℕ × (ℕ × ℕ)
abbrev Input := (Bool × Bool) × Layout
abbrev layoutEncoding := pairEncoding encodingNatBool (pairEncoding encodingNatBool encodingNatBool)
abbrev encoding := pairEncoding (pairEncoding encodingBoolBool encodingBoolBool) layoutEncoding
abbrev Poly := RationalSparseMachine.Poly

def constant (n : ℕ) (q : ℚ) : Poly := [(RationalInputMachine.zero n,q)]
def halfRoot (r : Layout) : Poly := RationalSparseMachine.mul (constant r.1 (1/2))
  (RationalSparseMachine.variable r.1 r.2.2)
def imaginaryHalf (r : Layout) : Poly := RationalSparseMachine.mul
  (RationalSparseMachine.variable r.1 r.2.1) (halfRoot r)

def entry (r : Input) (a b : Bool) : Poly :=
  if r.1.1 then
    if a then (if b != r.1.2 then RationalSparseMachine.neg (imaginaryHalf r.2) else imaginaryHalf r.2)
    else halfRoot r.2
  else constant r.2.1 (if a=b then 1 else 0)

def row (r : Input) (a b : Bool) : Poly :=
  RationalSparseMachine.sub (RationalMatrixMachine.matrix r.2.1 a b) (entry r a b)
def rows (r : Input) : List Poly :=
  [RationalMatrixMachine.guard r.2.1,row r false false,row r false true,row r true false,row r true true]

def typedConstant (v : ℕ) (q : ℚ) : Sparse.Poly v 1 := SparseTransform.constant (fun _ => q)

theorem constant_wire (n : ℕ) (q : ℚ) :
    constant n q=RationalInputMachine.rowWire (typedConstant n q) := by
  simp [constant,typedConstant,SparseTransform.constant,RationalInputMachine.zero,
    RationalInputMachine.rowWire,RationalInputMachine.termWire]
  exact (List.ofFn_const n (0 : ℕ)).symm

def typedEntry {v : ℕ} (native opposite : Bool) (imaginary sqrt : Fin v) (a b : Bool) : Sparse.Poly v 1 :=
  let half := Sparse.mul RationalCompiler.data (typedConstant v (1/2))
    (SparseTransform.variableCode RationalCompiler.data sqrt)
  let imagHalf := Sparse.mul RationalCompiler.data (SparseTransform.variableCode RationalCompiler.data imaginary) half
  if native then
    if a then (if b != opposite then Sparse.neg imagHalf else imagHalf) else half
  else typedConstant v (if a=b then 1 else 0)

theorem entry_wire {v : ℕ} (native opposite : Bool) (imaginary sqrt : Fin v) (a b : Bool) :
    entry ((native,opposite),(v,imaginary.val,sqrt.val)) a b=
      RationalInputMachine.rowWire (typedEntry native opposite imaginary sqrt a b) := by
  cases native <;> cases a <;> cases b <;> cases opposite <;>
    simp [entry,typedEntry,halfRoot,imaginaryHalf,constant_wire,
      RationalSparseMachine.variable_wire,RationalSparseMachine.mul_wire,RationalSparseMachine.neg_wire]

def typedRows {q : ℕ} (native opposite : Bool) (imaginary sqrt : Fin (5+q)) : List (Sparse.Poly (5+q) 1) :=
  [SparseTransform.guard RationalCompiler.data q,
    Sparse.sub (SparseTransform.matrix RationalCompiler.data q false false) (typedEntry native opposite imaginary sqrt false false),
    Sparse.sub (SparseTransform.matrix RationalCompiler.data q false true) (typedEntry native opposite imaginary sqrt false true),
    Sparse.sub (SparseTransform.matrix RationalCompiler.data q true false) (typedEntry native opposite imaginary sqrt true false),
    Sparse.sub (SparseTransform.matrix RationalCompiler.data q true true) (typedEntry native opposite imaginary sqrt true true)]

theorem rows_wire {q : ℕ} (native opposite : Bool) (imaginary sqrt : Fin (5+q)) :
    rows ((native,opposite),(5+q,imaginary.val,sqrt.val))=
      RationalInputMachine.bodyWire (typedRows native opposite imaginary sqrt) := by
  simp only [rows,row,entry_wire,RationalMatrixMachine.guard_wire,RationalMatrixMachine.matrix_wire,
    RationalSparseMachine.sub_wire,typedRows,RationalInputMachine.bodyWire,List.map_cons,List.map_nil]

noncomputable section
set_option backward.isDefEq.respectTransparency false

def constantExecutes (q : ℚ) : Executes encodingNatBool RationalSparseMachine.encoding (fun n => constant n q) :=
  (RationalInputMachine.Programs.zero.pair
    (Executes.ofComputes (constantComputes encodingNatBool rationalEncoding q))).comp
      (Executes.ofComputes (NegativeCertificateMachine.Lists.singleton RationalSparseMachine.termEncoding))

def halfExecutes : Executes layoutEncoding RationalSparseMachine.encoding halfRoot := by
  let n := Wiring.firstComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool)
  let indices := Wiring.secondComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool)
  let sqrt := indices.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  let root := (Executes.ofComputes (pairComputes n sqrt)).comp RationalSparseMachine.variableExecutes
  exact (((Executes.ofComputes n).comp (constantExecutes (1/2))).pair root).comp RationalSparseMachine.mulExecutes

def imaginaryHalfExecutes : Executes layoutEncoding RationalSparseMachine.encoding imaginaryHalf := by
  let n := Wiring.firstComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool)
  let imaginary := (Wiring.secondComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool)).andThen
    (Wiring.firstComputes encodingNatBool encodingNatBool)
  let root := (Executes.ofComputes (pairComputes n imaginary)).comp RationalSparseMachine.variableExecutes
  exact (root.pair halfExecutes).comp RationalSparseMachine.mulExecutes

private def choose {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
    {p : A → Bool} {f g : A → B} (test : Computes ea encodingBoolBool p)
    (yes : Executes ea eb f) (no : Executes ea eb g) : Executes ea eb (fun a => if p a then f a else g a) := by
  let select := ifComputes (Wiring.firstComputes encodingBoolBool (pairEncoding eb eb))
    ((Wiring.secondComputes encodingBoolBool (pairEncoding eb eb)).andThen (Wiring.firstComputes eb eb))
    ((Wiring.secondComputes encodingBoolBool (pairEncoding eb eb)).andThen (Wiring.secondComputes eb eb))
  exact ((Executes.ofComputes test).pair (yes.pair no)).comp (Executes.ofComputes select)

def entryExecutes (a b : Bool) : Executes encoding RationalSparseMachine.encoding (fun r => entry r a b) := by
  let flags := Wiring.firstComputes (pairEncoding encodingBoolBool encodingBoolBool) layoutEncoding
  let native := flags.andThen (Wiring.firstComputes encodingBoolBool encodingBoolBool)
  let opposite := flags.andThen (Wiring.secondComputes encodingBoolBool encodingBoolBool)
  let layout := Wiring.secondComputes (pairEncoding encodingBoolBool encodingBoolBool) layoutEncoding
  let width := layout.andThen (Wiring.firstComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool))
  let half := (Executes.ofComputes layout).comp halfExecutes
  let imaginaryHalf := (Executes.ofComputes layout).comp imaginaryHalfExecutes
  let sign := opposite.andThen (FiniteRecode.computes encodingBoolBool encodingBoolBool (fun o => b != o)
    1 (fun x => by cases x <;> decide))
  let signed := choose encoding RationalSparseMachine.encoding sign
    (imaginaryHalf.comp (Executes.ofComputes RationalSparseMachine.negComputes)) imaginaryHalf
  cases a with
  | false => exact choose encoding RationalSparseMachine.encoding native half ((Executes.ofComputes width).comp (constantExecutes (if false=b then 1 else 0)))
  | true => exact choose encoding RationalSparseMachine.encoding native signed ((Executes.ofComputes width).comp (constantExecutes (if true=b then 1 else 0)))

def rowExecutes (a b : Bool) : Executes encoding RationalSparseMachine.encoding (fun r => row r a b) := by
  let width := (Wiring.secondComputes (pairEncoding encodingBoolBool encodingBoolBool) layoutEncoding).andThen
    (Wiring.firstComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool))
  exact (((Executes.ofComputes width).comp (RationalMatrixMachine.matrixAt a b)).pair (entryExecutes a b)).comp
    (Executes.ofComputes RationalSparseMachine.subComputes)

def executes : Executes encoding RationalSparseMachine.familyEncoding rows := by
  let width := (Wiring.secondComputes (pairEncoding encodingBoolBool encodingBoolBool) layoutEncoding).andThen
    (Wiring.firstComputes encodingNatBool (pairEncoding encodingNatBool encodingNatBool))
  let empty := Executes.ofComputes (constantComputes encoding RationalSparseMachine.familyEncoding [])
  exact RationalInputMachine.Programs.consExec RationalSparseMachine.encoding
    ((Executes.ofComputes width).comp RationalMatrixMachine.guardExecutes)
    (RationalInputMachine.Programs.consExec RationalSparseMachine.encoding (rowExecutes false false)
    (RationalInputMachine.Programs.consExec RationalSparseMachine.encoding (rowExecutes false true)
    (RationalInputMachine.Programs.consExec RationalSparseMachine.encoding (rowExecutes true false)
    (RationalInputMachine.Programs.consExec RationalSparseMachine.encoding (rowExecutes true true) empty))))

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorBasis
