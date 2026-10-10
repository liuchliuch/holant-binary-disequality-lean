import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.Certificates
import Holant.Proofs.Algorithms.TransformRecognition.RationalSparseMachine
import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.API


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes coordinatesEncoding)
open ComplexIsolation
open CertificateMachine (polynomialEncoding termEncoding certificateEncoding rootEncoding)
noncomputable section

namespace CodePrograms
abbrev pairEncoding := FixedFieldMachines.pairEncoding polynomialEncoding polynomialEncoding

def negComputes : Computes polynomialEncoding polynomialEncoding Code.neg :=
  WireLists.mapComputes termEncoding termEncoding _ (pairComputes
    (Wiring.firstComputes encodingNatBool rationalEncoding)
    ((Wiring.secondComputes encodingNatBool rationalEncoding).andThen
      Holant.LocalDrafts.TraversalCompletion.RationalLP.Comparison.rationalNegate))

def subComputes : Computes pairEncoding polynomialEncoding (fun p => Code.sub p.1 p.2) :=
  (pairComputes (Wiring.firstComputes polynomialEncoding polynomialEncoding)
    ((Wiring.secondComputes polynomialEncoding polynomialEncoding).andThen negComputes)).andThen
      (WireLists.append termEncoding)

def termComputes : Computes (FixedFieldMachines.pairEncoding termEncoding termEncoding)
    termEncoding (fun p => Code.termMul p.1 p.2) := by
  let a := Wiring.firstComputes termEncoding termEncoding
  let b := Wiring.secondComputes termEncoding termEncoding
  let exponent := Wiring.firstComputes encodingNatBool rationalEncoding
  let coefficient := Wiring.secondComputes encodingNatBool rationalEncoding
  exact pairComputes
    ((pairComputes (a.andThen exponent) (b.andThen exponent)).andThen RationalInputMachine.Programs.add)
    (CertificateMachine.Scalars.mul (a.andThen coefficient) (b.andThen coefficient))

def rowComputes : Computes (FixedFieldMachines.pairEncoding termEncoding polynomialEncoding)
    polynomialEncoding (fun p => p.2.map (Code.termMul p.1)) :=
  mapListComputes termEncoding termEncoding termEncoding Code.termMul termComputes

def mulExecutes : Executes pairEncoding polynomialEncoding (fun p => Code.mul p.1 p.2) := by
  let p := Wiring.firstComputes polynomialEncoding polynomialEncoding
  let q := Wiring.secondComputes polynomialEncoding polynomialEncoding
  let context := Wiring.firstComputes pairEncoding termEncoding
  let t := Wiring.secondComputes pairEncoding termEncoding
  let cell := (Executes.ofComputes (pairComputes t (context.andThen q))).comp
    (Executes.ofComputes rowComputes)
  let rows := NegativeCertificateMachine.Lists.map pairEncoding termEncoding polynomialEncoding
    (Executes.ofComputes p) (fun p t => p.2.map (Code.termMul t)) cell
  exact (rows.comp (Executes.ofComputes (WireLists.flatten termEncoding))).congr
    (fun p => by simp only [Code.mul,List.flatMap_def])

abbrev coefficientEncoding := FixedFieldMachines.pairEncoding polynomialEncoding encodingNatBool
def maskComputes : Computes (FixedFieldMachines.pairEncoding coefficientEncoding termEncoding)
    rationalEncoding (fun p => if p.2.1=p.1.2 then p.2.2 else 0) := by
  let arg := Wiring.firstComputes coefficientEncoding termEncoding
  let t := Wiring.secondComputes coefficientEncoding termEncoding
  let key := arg.andThen (Wiring.secondComputes polynomialEncoding encodingNatBool)
  let exponent := t.andThen (Wiring.firstComputes encodingNatBool rationalEncoding)
  let value := t.andThen (Wiring.secondComputes encodingNatBool rationalEncoding)
  exact congrComputes (ifComputes (AccessPrograms.eqNat exponent key) value
    (constantComputes _ rationalEncoding 0))
      (fun x => by simp only [Function.comp_apply,decide_eq_true_eq])

def coefficientExecutes : Executes coefficientEncoding rationalEncoding (fun p => Code.coeff p.1 p.2) := by
  let terms := Wiring.firstComputes polynomialEncoding encodingNatBool
  let masked := AccessPrograms.map termEncoding rationalEncoding terms
    (fun p t => if t.1=p.2 then t.2 else 0) maskComputes
  exact (Executes.ofComputes masked).comp CommonFieldMachine.Companion.rationalSum

def zeroCell : Executes (FixedFieldMachines.pairEncoding polynomialEncoding termEncoding)
    encodingBoolBool (fun p => decide (Code.coeff p.1 p.2.1=0)) :=
  ((Executes.ofComputes (pairComputes
    (Wiring.firstComputes polynomialEncoding termEncoding)
    ((Wiring.secondComputes polynomialEncoding termEncoding).andThen
      (Wiring.firstComputes encodingNatBool rationalEncoding)))).comp coefficientExecutes).comp
        (Executes.ofComputes CommonFieldMachine.CoordinatePrimitives.scalarZero)

def zeroExecutes : Executes polynomialEncoding encodingBoolBool Code.isZero := by
  let checks := NegativeCertificateMachine.Lists.map polynomialEncoding termEncoding encodingBoolBool
    (Executes.ofComputes (identityComputes polynomialEncoding))
    (fun p t => decide (Code.coeff p t.1=0)) zeroCell
  exact (checks.comp (Executes.ofComputes CommonFieldMachine.CoordinatePrimitives.allTrue)).congr
    (fun p => by simp [Code.isZero,List.all_map])

def equalExecutes : Executes pairEncoding encodingBoolBool (fun p => Code.equal p.1 p.2) :=
  (Executes.ofComputes subComputes).comp zeroExecutes

def denseComputes : Computes coordinatesEncoding polynomialEncoding Code.dense := by
  let cell : Computes (FixedFieldMachines.pairEncoding coordinatesEncoding GraphPreprocessing.UnaryBinary.unaryEncoding)
      termEncoding (fun p => (p.2,p.1.getD p.2 0)) :=
    pairComputes ((Wiring.secondComputes coordinatesEncoding GraphPreprocessing.UnaryBinary.unaryEncoding).andThen
      GraphPreprocessing.UnaryBinary.computes)
      (AccessPrograms.get rationalEncoding 0
        (Wiring.firstComputes coordinatesEncoding GraphPreprocessing.UnaryBinary.unaryEncoding)
        (Wiring.secondComputes coordinatesEncoding GraphPreprocessing.UnaryBinary.unaryEncoding))
  exact WireLists.tabulate coordinatesEncoding termEncoding List.length
    (WireLists.lengthComputes rationalEncoding) (fun v i => (i,v.getD i 0)) cell
end CodePrograms

abbrev EvidenceWire := Bool × (Code.Poly × (Code.Poly × (Code.Poly × (Code.Poly × Certificate))))
abbrev evidenceTail₄Encoding := pairEncoding polynomialEncoding certificateEncoding
abbrev evidenceTail₃Encoding := pairEncoding polynomialEncoding evidenceTail₄Encoding
abbrev evidenceTail₂Encoding := pairEncoding polynomialEncoding evidenceTail₃Encoding
abbrev evidenceTail₁Encoding := pairEncoding polynomialEncoding evidenceTail₂Encoding
abbrev evidenceWireEncoding := pairEncoding encodingBoolBool evidenceTail₁Encoding

def evidenceWire (e : Evidence) : EvidenceWire :=
  (e.zero,e.factor,e.relationQuotient,e.left,e.right,e.certificate)
def evidenceUnwire (e : EvidenceWire) : Evidence :=
  ⟨e.1,e.2.1,e.2.2.1,e.2.2.2.1,e.2.2.2.2.1,e.2.2.2.2.2⟩
@[simp] theorem evidenceUnwire_wire (e : Evidence) : evidenceUnwire (evidenceWire e)=e := by cases e; rfl
@[simp] theorem evidenceWire_unwire (e : EvidenceWire) : evidenceWire (evidenceUnwire e)=e := by
  rcases e with ⟨a,b,c,d,f,t⟩; rfl
def evidenceEncoding : Encoding Evidence Bool where
  encode e := evidenceWireEncoding.encode (evidenceWire e)
  decode w := (evidenceWireEncoding.decode w).map evidenceUnwire
  decode_encode e := by rw [Encoding.decode_encode]; rfl

abbrev Input := RootCode × (Code.Poly × Evidence)
abbrev tailEncoding := pairEncoding polynomialEncoding evidenceEncoding
abbrev inputEncoding := pairEncoding rootEncoding tailEncoding

def evidenceTag : Computes evidenceEncoding encodingBoolBool Evidence.zero :=
  recode (Wiring.firstComputes encodingBoolBool evidenceTail₁Encoding)
    evidenceWire (fun _ => rfl) (fun _ => rfl)
def evidenceTail₁ : Computes evidenceEncoding evidenceTail₁Encoding (fun e => (e.factor,e.relationQuotient,e.left,e.right,e.certificate)) :=
  recode (Wiring.secondComputes encodingBoolBool evidenceTail₁Encoding)
    evidenceWire (fun _ => rfl) (fun _ => rfl)
def evidenceFactor : Computes evidenceEncoding polynomialEncoding Evidence.factor :=
  evidenceTail₁.andThen (Wiring.firstComputes _ _)
def evidenceTail₂ : Computes evidenceEncoding evidenceTail₂Encoding (fun e => (e.relationQuotient,e.left,e.right,e.certificate)) :=
  evidenceTail₁.andThen (Wiring.secondComputes _ _)
def evidenceQuotient : Computes evidenceEncoding polynomialEncoding Evidence.relationQuotient :=
  evidenceTail₂.andThen (Wiring.firstComputes _ _)
def evidenceTail₃ : Computes evidenceEncoding evidenceTail₃Encoding (fun e => (e.left,e.right,e.certificate)) :=
  evidenceTail₂.andThen (Wiring.secondComputes _ _)
def evidenceLeft : Computes evidenceEncoding polynomialEncoding Evidence.left :=
  evidenceTail₃.andThen (Wiring.firstComputes _ _)
def evidenceTail₄ : Computes evidenceEncoding evidenceTail₄Encoding (fun e => (e.right,e.certificate)) :=
  evidenceTail₃.andThen (Wiring.secondComputes _ _)
def evidenceRight : Computes evidenceEncoding polynomialEncoding Evidence.right :=
  evidenceTail₄.andThen (Wiring.firstComputes _ _)
def evidenceCertificate : Computes evidenceEncoding certificateEncoding Evidence.certificate :=
  evidenceTail₄.andThen (Wiring.secondComputes _ _)
def root : Computes inputEncoding rootEncoding (fun x : Input => x.1) := Wiring.firstComputes _ _
def tail : Computes inputEncoding tailEncoding (fun x : Input => x.2) := Wiring.secondComputes _ _
def query : Computes inputEncoding polynomialEncoding (fun x : Input => x.2.1) :=
  tail.andThen (Wiring.firstComputes _ _)
def evidence : Computes inputEncoding evidenceEncoding (fun x : Input => x.2.2) :=
  tail.andThen (Wiring.secondComputes _ _)
def rootCoefficients : Computes rootEncoding polynomialEncoding RootCode.coefficients :=
  recode (Wiring.firstComputes polynomialEncoding CertificateMachine.rectangleEncoding)
    (fun c : RootCode => (c.coefficients,c.rectangle)) (fun _ => rfl) (fun _ => rfl)
def rootRectangle : Computes rootEncoding CertificateMachine.rectangleEncoding RootCode.rectangle :=
  recode (Wiring.secondComputes polynomialEncoding CertificateMachine.rectangleEncoding)
    (fun c : RootCode => (c.coefficients,c.rectangle)) (fun _ => rfl) (fun _ => rfl)

def insideComputes : Computes inputEncoding encodingBoolBool (fun x : Input => inside x.1 x.2.2.certificate) := by
  let t := evidence.andThen evidenceCertificate
  let b := t.andThen PositiveCertificateMachine.certificateBoxComputes
  let r := root.andThen rootRectangle
  exact congrComputes ((pairComputes b r).andThen CommonFieldMachine.BoxPrimitives.inside)
    (fun x => by rfl)

def andExecutes {A : Type} {ea : Encoding A Bool} {f g : A → Bool}
    (u : Executes ea encodingBoolBool f) (v : Executes ea encodingBoolBool g) :
    Executes ea encodingBoolBool (fun a => f a && g a) :=
  (u.pair v).comp (Executes.ofComputes
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes
      (fun p : Bool × Bool => p.1 && p.2)))

def commonExecutes : Executes inputEncoding encodingBoolBool (fun x : Input => commonCheck x.1 x.2.2) := by
  let g := evidence.andThen evidenceFactor
  let a := evidence.andThen evidenceQuotient
  let p := root.andThen rootCoefficients
  let t := evidence.andThen evidenceCertificate
  let rootChecker := CertificateMachine.computes
  let rootRun : Executes CertificateMachine.inputEncoding encodingBoolBool
      (fun x : CertificateMachine.Input => x.2.check x.1) :=
    ⟨rootChecker.machine,fun x => rootChecker.time (CertificateMachine.inputEncoding.encode x).length,
      rootChecker.outputs⟩
  let certified := (Executes.ofComputes (pairComputes g t)).comp rootRun
  let factor := (Executes.ofComputes (pairComputes g a)).comp CodePrograms.mulExecutes
  let relation := (factor.pair (Executes.ofComputes p)).comp CodePrograms.equalExecutes
  exact andExecutes (andExecutes certified (Executes.ofComputes insideComputes)) relation

def selectValue : Computes (pairEncoding encodingBoolBool (pairEncoding encodingBoolBool encodingBoolBool))
    encodingBoolBool (fun p : Bool × (Bool × Bool) => if p.1 then p.2.1 else p.2.2) :=
  ifComputes (Wiring.firstComputes _ _)
    ((Wiring.secondComputes _ _).andThen (Wiring.firstComputes _ _))
    ((Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _))

def valueExecutes : Executes inputEncoding encodingBoolBool (fun x : Input => valueCheck x.2.1 x.2.2) := by
  let g := Executes.ofComputes (evidence.andThen evidenceFactor)
  let l := Executes.ofComputes (evidence.andThen evidenceLeft)
  let r := Executes.ofComputes (evidence.andThen evidenceRight)
  let q := Executes.ofComputes query
  let positive := (((g.pair l).comp CodePrograms.mulExecutes).pair q).comp CodePrograms.equalExecutes
  let lg := (l.pair g).comp CodePrograms.mulExecutes
  let rq := (r.pair q).comp CodePrograms.mulExecutes
  let sum := (lg.pair rq).comp (Executes.ofComputes (WireLists.append termEncoding))
  let negative := (sum.pair (Executes.ofComputes (constantComputes inputEncoding polynomialEncoding Code.one))).comp
    CodePrograms.equalExecutes
  exact ((Executes.ofComputes (evidence.andThen evidenceTag)).pair (positive.pair negative)).comp
    (Executes.ofComputes selectValue)

/-- A concrete program and exact recursively composed run for every finite
input. Source correctness/termination/root promises are not checker inputs. -/
def executes : Executes inputEncoding encodingBoolBool (fun x : Input => check x.1 x.2.1 x.2.2) :=
  andExecutes commonExecutes valueExecutes
def outputs (x : Input) : TM2OutputsInTime executes.machine.computer (inputEncoding.encode x)
    (some (encodingBoolBool.encode (check x.1 x.2.1 x.2.2))) (executes.cost x) := executes.outputs x

theorem primitive_bound (x : Input) :
    primitiveCost executes.machine (outputs x).steps
      (some (initList executes.machine.computer (inputEncoding.encode x))) ≤
        executes.cost x*executes.machine.primitiveBudget := executes.primitive_bound x

theorem prefix_bits (x : Input) {i : ℕ} (hi : i≤(outputs x).steps)
    {s : executes.machine.Config}
    (hs : (fun p => p.bind executes.machine.computer.step)^[i]
      (some (initList executes.machine.computer (inputEncoding.encode x)))=some s) :
    stackSize s.stk ≤ (inputEncoding.encode x).length+executes.cost x*executes.machine.primitiveBudget := by
  have h := executes.machine.run_size_le _ s i hs
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hi.trans (outputs x).steps_le_m)) _)

end
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
