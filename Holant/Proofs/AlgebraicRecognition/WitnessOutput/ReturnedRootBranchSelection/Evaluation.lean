import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.Search
import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.RightFold
import Holant.Proofs.AlgebraicRecognition.WitnessOutput.BranchConsumers.Programs


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
open Polynomial Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes coordinatesEncoding)
open ComplexIsolation
open CertificateMachine (polynomialEncoding termEncoding)

namespace Evaluate
abbrev Variables := List (List ℚ)
abbrev variablesEncoding := PositiveCertificateMachine.vectorsEncoding
abbrev Term := RationalInputMachine.Term
abbrev Row := RationalInputMachine.Row
abbrev Body := RationalInputMachine.Body

def powers (vs : Variables) (t : Term) : List Code.Poly :=
  (List.range t.1.length).map (fun i => Code.power (Code.dense (vs.getD i [])) (t.1.getD i 0))
def term (vs : Variables) (t : Term) : Code.Poly :=
  Code.mul [(0,t.2)] (Code.product (powers vs t))
def row (vs : Variables) (p : Row) : Code.Poly := p.flatMap (term vs)
def body (o : Output) (S : Body) : List Code.Poly := S.map (row o.variables)

noncomputable def termValue (z : ℂ) (vs : Variables) (t : Term) : ℂ :=
  (t.2 : ℂ)*((List.range t.1.length).map
    (fun i => BranchConsumers.decodeList z (vs.getD i [])^t.1.getD i 0)).prod
noncomputable def rowValue (z : ℂ) (vs : Variables) (p : Row) : ℂ :=
  (p.map (termValue z vs)).sum

theorem term_correct (z : ℂ) (vs : Variables) (t : Term) :
    Polynomial.aeval z (term vs t).polynomial=termValue z vs t := by
  have hc : Polynomial.aeval z (RationalPolynomialCode.polynomial [(0,t.2)])=
      (t.2 : ℂ) := by
    simp [RationalPolynomialCode.polynomial,Polynomial.aeval_monomial]
  rw [term,Code.polynomial_mul,map_mul,hc,Code.polynomial_product,map_list_prod]
  simp only [powers,List.map_map,Function.comp_def,Code.polynomial_power,
    map_pow,Code.dense_correct,termValue]

theorem row_correct (z : ℂ) (vs : Variables) (p : Row) :
    Polynomial.aeval z (row vs p).polynomial=rowValue z vs p := by
  induction p with
  | nil => simp [row,rowValue,RationalPolynomialCode.polynomial]
  | cons t ts ih =>
    change Polynomial.aeval z
        (RationalPolynomialCode.polynomial (term vs t ++ row vs ts))=
      termValue z vs t + rowValue z vs ts
    rw [RationalPolynomialCode.polynomial_append,map_add,term_correct,ih]

noncomputable section
abbrev powerStateEncoding := pairEncoding polynomialEncoding polynomialEncoding
def powerStep (s : Code.Poly × Code.Poly) := (s.1,Code.mul s.2 s.1)
def powerStepExecutes : Executes powerStateEncoding powerStateEncoding powerStep :=
  (Executes.ofComputes (Wiring.firstComputes polynomialEncoding polynomialEncoding)).pair
    ((Executes.ofComputes (Wiring.swapComputes polynomialEncoding polynomialEncoding)).comp
      CodePrograms.mulExecutes)
theorem power_iterate (p : Code.Poly) (k : ℕ) :
    (powerStep^[k]) (p,Code.one)=(p,Code.power p k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl
abbrev powerEncoding := pairEncoding polynomialEncoding encodingNatBool
def powerExecutes : Executes powerEncoding polynomialEncoding (fun p => Code.power p.1 p.2) := by
  let p := Wiring.firstComputes polynomialEncoding encodingNatBool
  let k := Wiring.secondComputes polynomialEncoding encodingNatBool
  let start := Executes.ofComputes (pairComputes k
    (pairComputes p (constantComputes powerEncoding polynomialEncoding Code.one)))
  let loop := CommonFieldMachine.Iteration.executes powerStateEncoding powerStepExecutes
  let finish := Executes.ofComputes (Wiring.secondComputes polynomialEncoding polynomialEncoding)
  exact ((start.comp loop).comp finish).congr
    (fun p => by change ((powerStep^[p.2]) (p.1,Code.one)).2=_; rw [power_iterate])

abbrev polysEncoding := framedListEncoding polynomialEncoding
abbrev productEncoding := pairEncoding encodingBoolBool polysEncoding
def productExecutes : Executes polysEncoding polynomialEncoding Code.product := by
  let start := Executes.ofComputes (pairComputes
    (constantComputes polysEncoding encodingBoolBool false)
    (pairComputes (identityComputes polysEncoding)
      (constantComputes polysEncoding polynomialEncoding Code.one)))
  let cell := (Executes.ofComputes (Wiring.secondComputes encodingBoolBool CodePrograms.pairEncoding)).comp
    CodePrograms.mulExecutes
  exact (start.comp (PositiveCertificateMachine.RightFold.executes encodingBoolBool
    polynomialEncoding polynomialEncoding (fun _ p q => Code.mul p q) [] cell)).congr
      (fun _ => rfl)

abbrev termInputEncoding := pairEncoding variablesEncoding RationalInputMachine.termEncoding
abbrev powerCellEncoding := pairEncoding termInputEncoding encodingNatBool
def powerCellExecutes : Executes powerCellEncoding polynomialEncoding
    (fun p => Code.power (Code.dense (p.1.1.getD p.2 [])) (p.1.2.1.getD p.2 0)) := by
  let context := Wiring.firstComputes termInputEncoding encodingNatBool
  let i := Wiring.secondComputes termInputEncoding encodingNatBool
  let vs := context.andThen (Wiring.firstComputes variablesEncoding RationalInputMachine.termEncoding)
  let t := context.andThen (Wiring.secondComputes variablesEncoding RationalInputMachine.termEncoding)
  let es := t.andThen (Wiring.firstComputes NegativeCertificateMachine.exponentEncoding rationalEncoding)
  let v := ((Executes.ofComputes (pairComputes vs i)).comp
    (NegativeCertificateMachine.Lists.lookup coordinatesEncoding [])).comp
      (Executes.ofComputes CodePrograms.denseComputes)
  let k := (Executes.ofComputes (pairComputes es i)).comp
    (NegativeCertificateMachine.Lists.lookup encodingNatBool 0)
  exact (v.pair k).comp powerExecutes

def powersExecutes : Executes termInputEncoding polysEncoding (fun p => powers p.1 p.2) := by
  let exponents := (Wiring.secondComputes variablesEncoding RationalInputMachine.termEncoding).andThen
    (Wiring.firstComputes NegativeCertificateMachine.exponentEncoding rationalEncoding)
  let count := (exponents.andThen (WireLists.lengthComputes encodingNatBool)).andThen
    GraphPreprocessing.UnaryBinary.computes
  exact NegativeCertificateMachine.Lists.map termInputEncoding encodingNatBool polynomialEncoding
    ((Executes.ofComputes count).comp RationalInputMachine.Programs.range)
    (fun p i => Code.power (Code.dense (p.1.getD i [])) (p.2.1.getD i 0)) powerCellExecutes

def coefficientComputes : Computes termInputEncoding polynomialEncoding (fun p => [(0,p.2.2)]) :=
  (pairComputes (constantComputes termInputEncoding encodingNatBool 0)
    ((Wiring.secondComputes variablesEncoding RationalInputMachine.termEncoding).andThen
      (Wiring.secondComputes NegativeCertificateMachine.exponentEncoding rationalEncoding))).andThen
        (NegativeCertificateMachine.Lists.singleton termEncoding)

def termExecutes : Executes termInputEncoding polynomialEncoding (fun p => term p.1 p.2) :=
  ((Executes.ofComputes coefficientComputes).pair (powersExecutes.comp productExecutes)).comp
    CodePrograms.mulExecutes

abbrev rowInputEncoding := pairEncoding variablesEncoding RationalInputMachine.rowEncoding
def rowExecutes : Executes rowInputEncoding polynomialEncoding (fun p => row p.1 p.2) :=
  ((Executes.mapList variablesEncoding RationalInputMachine.termEncoding polynomialEncoding
    term termExecutes).comp (Executes.ofComputes (WireLists.flatten termEncoding))).congr
      (fun p => by simp only [row,List.flatMap_def])

abbrev bodyInputEncoding := pairEncoding outputEncoding RationalInputMachine.bodyEncoding
def bodyExecutes : Executes bodyInputEncoding polysEncoding (fun p => body p.1 p.2) := by
  let o := Wiring.firstComputes bodyInputEncoding RationalInputMachine.rowEncoding
  let r := Wiring.secondComputes bodyInputEncoding RationalInputMachine.rowEncoding
  let context := o.andThen (Wiring.firstComputes outputEncoding RationalInputMachine.bodyEncoding)
  let cell := (Executes.ofComputes (pairComputes
    (context.andThen BranchConsumers.variablesComputes) r)).comp rowExecutes
  exact NegativeCertificateMachine.Lists.map bodyInputEncoding RationalInputMachine.rowEncoding polynomialEncoding
    (Executes.ofComputes (Wiring.secondComputes outputEncoding RationalInputMachine.bodyEncoding))
    (fun p r => row p.1.variables r) cell

def outputs (o : Output) (S : Body) : TM2OutputsInTime bodyExecutes.machine.computer
    (bodyInputEncoding.encode (o,S)) (some (polysEncoding.encode (body o S))) (bodyExecutes.cost (o,S)) :=
  bodyExecutes.outputs (o,S)
end
end Evaluate
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
