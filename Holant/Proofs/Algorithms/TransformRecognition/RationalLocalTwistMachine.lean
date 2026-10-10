import Holant.Proofs.Algorithms.TransformRecognition.RationalProductRowsMachine
import Holant.Proofs.Algorithms.TransformRecognition.SymbolicPhaseCoefficients


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalLocalTwistMachine
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Word := RationalTensorMachine.Word
abbrev wordsEncoding := pairEncoding RationalTensorMachine.wordEncoding RationalTensorMachine.wordEncoding
abbrev tailEncoding := pairEncoding encodingNatBool wordsEncoding
abbrev Input := ℕ × (ℕ × (Word × Word))
abbrev encoding := pairEncoding encodingNatBool tailEncoding
abbrev cellEncoding := pairEncoding encoding encodingNatBool

def factor (r : Input) (j : ℕ) : RationalSparseMachine.Poly :=
  if r.2.2.1.getD j false && r.2.2.2.getD j false then
    RationalSparseMachine.variable r.1 r.2.1 else RationalSparseMachine.one r.1
def factors (r : Input) := (List.range r.2.2.1.length).map (factor r)
def value (r : Input) := RationalSparseMachine.product r.1 (factors r)

noncomputable section
def width := Wiring.firstComputes encodingNatBool tailEncoding
def tail := Wiring.secondComputes encodingNatBool tailEncoding
def eighth := tail.andThen (Wiring.firstComputes encodingNatBool wordsEncoding)
def words := tail.andThen (Wiring.secondComputes encodingNatBool wordsEncoding)
def alpha := words.andThen (Wiring.firstComputes RationalTensorMachine.wordEncoding RationalTensorMachine.wordEncoding)
def assignment := words.andThen (Wiring.secondComputes RationalTensorMachine.wordEncoding RationalTensorMachine.wordEncoding)

def factorExecutes : Executes cellEncoding RationalSparseMachine.encoding
    (fun r : Input × ℕ => factor r.1 r.2) := by
  let context := Wiring.firstComputes encoding encodingNatBool
  let j := Wiring.secondComputes encoding encodingNatBool
  let a := (Executes.ofComputes (pairComputes (context.andThen alpha) j)).comp
    (NegativeCertificateMachine.Lists.lookup encodingBoolBool false)
  let x := (Executes.ofComputes (pairComputes (context.andThen assignment) j)).comp
    (NegativeCertificateMachine.Lists.lookup encodingBoolBool false)
  let both := GraphPreprocessing.FiniteRecode.computes
    (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p : Bool × Bool => p.1 && p.2) 4
    (fun p => by rcases p with ⟨b,c⟩; cases b <;> cases c <;> decide)
  let flag := (a.pair x).comp (Executes.ofComputes both)
  let varPoly := (Executes.ofComputes (pairComputes (context.andThen width) (context.andThen eighth))).comp
    RationalSparseMachine.variableExecutes
  let one := (Executes.ofComputes (context.andThen width)).comp RationalSparseMachine.oneExecutes
  let choose := ifComputes (Wiring.firstComputes encodingBoolBool RationalSparseMachine.pairEncoding)
    ((Wiring.secondComputes encodingBoolBool RationalSparseMachine.pairEncoding).andThen
      (Wiring.firstComputes RationalSparseMachine.encoding RationalSparseMachine.encoding))
    ((Wiring.secondComputes encodingBoolBool RationalSparseMachine.pairEncoding).andThen
      (Wiring.secondComputes RationalSparseMachine.encoding RationalSparseMachine.encoding))
  exact (flag.pair (varPoly.pair one)).comp (Executes.ofComputes choose)

def factorsExecutes : Executes encoding RationalSparseMachine.familyEncoding factors :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool RationalSparseMachine.encoding
    ((Executes.ofComputes ((alpha.andThen (WireLists.lengthComputes encodingBoolBool)).andThen
      GraphPreprocessing.UnaryBinary.computes)).comp RationalInputMachine.Programs.range)
    factor factorExecutes

def executes : Executes encoding RationalSparseMachine.encoding value :=
  ((Executes.ofComputes width).pair factorsExecutes).comp RationalSparseMachine.productExecutes
end

theorem factor_source {n v : ℕ} (eighth : Fin v) (a x : Fin n → Bool) (j : Fin n) :
    factor (v,eighth.val,List.ofFn a,List.ofFn x) j.val =
      RationalInputMachine.rowWire (if a j && x j then
        SparseTransform.variableCode RationalCompiler.data eighth else Sparse.one RationalCompiler.data) := by
  simp only [factor,Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn]
  cases h : a j && x j <;>
    simp only [h,Bool.false_eq_true,ite_false,ite_true,RationalSparseMachine.variable_wire,
      RationalSparseMachine.one_wire]

theorem value_source {n v : ℕ} (eighth : Fin v) (a x : Fin n → Bool) :
    value (v,eighth.val,List.ofFn a,List.ofFn x) =
      RationalInputMachine.rowWire (SymbolicPhaseCoefficients.twistCoefficient eighth a x) := by
  have hf : factors (v,eighth.val,List.ofFn a,List.ofFn x) =
      (List.ofFn (fun j => if a j && x j then
        SparseTransform.variableCode RationalCompiler.data eighth else Sparse.one RationalCompiler.data)).map
        RationalInputMachine.rowWire := by
    unfold factors
    simp only [List.length_ofFn]
    change CommonFieldMachine.Coordinates.tab n
      (factor (v,eighth.val,List.ofFn a,List.ofFn x)) = _
    rw [CommonFieldMachine.Coordinates.tab_ofFn,List.map_ofFn]
    congr 1
    funext j
    simpa only [Function.comp_def] using factor_source eighth a x j
  unfold value
  rw [hf,RationalSparseMachine.product_wire]
  rfl

end Holant.LocalDrafts.MainChain.TransformRecognition.RationalLocalTwistMachine
