import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.FirstIndex


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

namespace Programs
noncomputable section
variable {A B : Type} {ea : Encoding A Bool}

def cons (eb : Encoding B Bool) {f : A → B} {g : A → List B}
    (u : Computes ea eb f) (v : Computes ea (framedListEncoding eb) g) :
    Computes ea (framedListEncoding eb) (fun a => f a :: g a) :=
  (pairComputes u v).andThen (StructuralListMachine.consComputes eb)

def consExec (eb : Encoding B Bool) {f : A → B} {g : A → List B}
    (u : Executes ea eb f) (v : Executes ea (framedListEncoding eb) g) :
    Executes ea (framedListEncoding eb) (fun a => f a :: g a) :=
  (Executes.pair u v).comp (Executes.ofComputes (StructuralListMachine.consComputes eb))

def add : Computes (pairEncoding encodingNatBool encodingNatBool) encodingNatBool
    (fun p => p.1+p.2) := Endpoints.prepareArithmeticComputes.andThen BinaryCompose.additionComputes

def successor : Computes encodingNatBool encodingNatBool (fun n => n+1) :=
  (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool encodingNatBool 1)).andThen add

def range : Executes encodingNatBool (framedListEncoding encodingNatBool) List.range :=
  Executes.congr (NegativeCertificateMachine.Lists.toUnary.comp
    (Executes.ofComputes (ComponentSelection.UnaryRange.computes.andThen
      (WireLists.mapComputes UnaryBinary.unaryEncoding encodingNatBool id UnaryBinary.computes))))
        (fun n => by simp only [Function.comp_apply,id_eq,List.map_id])

def coefficients : Computes bodyEncoding CommonFieldMachine.coordinatesEncoding RationalInputMachine.coefficients := by
  let row := WireLists.mapComputes termEncoding rationalEncoding Prod.snd
    (Wiring.secondComputes NegativeCertificateMachine.exponentEncoding rationalEncoding)
  let flat := (WireLists.mapComputes rowEncoding CommonFieldMachine.coordinatesEncoding
    (fun p => p.map Prod.snd) row).andThen (WireLists.flatten rationalEncoding)
  exact congrComputes (cons rationalEncoding (constantComputes bodyEncoding rationalEncoding 1)
    (cons rationalEncoding (constantComputes bodyEncoding rationalEncoding (-1)) flat))
      (fun S => by simp only [Function.comp_apply,RationalInputMachine.coefficients,List.flatMap_def])

def rootCode : Computes rationalEncoding ComplexIsolation.CertificateMachine.rootEncoding RationalRootCode.code := by
  let q := identityComputes rationalEncoding
  let one := constantComputes rationalEncoding rationalEncoding 1
  let neg := q.andThen Holant.LocalDrafts.TraversalCompletion.RationalLP.Comparison.rationalNegate
  let leading := constantComputes rationalEncoding ComplexIsolation.CertificateMachine.termEncoding (1,1)
  let constant := pairComputes (constantComputes rationalEncoding encodingNatBool 0) neg
  let poly := cons ComplexIsolation.CertificateMachine.termEncoding leading
    (constant.andThen (NegativeCertificateMachine.Lists.singleton ComplexIsolation.CertificateMachine.termEncoding))
  let real := pairComputes (ComplexIsolation.CertificateMachine.Scalars.sub q one)
    (ComplexIsolation.CertificateMachine.Scalars.add q one)
  let rect := pairComputes real
    (constantComputes rationalEncoding ComplexIsolation.CertificateMachine.gaussianEncoding (-1,1))
  exact recode (pairComputes poly rect) id (fun _ => rfl) (fun _ => rfl)

def zero : Executes encodingNatBool NegativeCertificateMachine.exponentEncoding RationalInputMachine.zero :=
  NegativeCertificateMachine.Lists.toUnary.comp (Executes.ofComputes (WireLists.replicate encodingNatBool 0))

abbrev hitEncoding := pairEncoding encodingNatBool encodingNatBool
def indicator (j : ℕ) : Computes encodingNatBool encodingNatBool (fun i => if i=j then 1 else 0) :=
  congrComputes (ifComputes ((pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool encodingNatBool j)).andThen Endpoints.equalComputes)
      (constantComputes encodingNatBool encodingNatBool 1) (constantComputes encodingNatBool encodingNatBool 0))
        (fun i => by simp only [Function.comp_apply,id_eq,decide_eq_true_eq])

def hitCell : Computes (pairEncoding hitEncoding encodingNatBool) encodingNatBool
    (fun p => if p.2=p.1.2 then 1 else 0) := by
  let j := (Wiring.firstComputes hitEncoding encodingNatBool).andThen
    (Wiring.secondComputes encodingNatBool encodingNatBool)
  let i := Wiring.secondComputes hitEncoding encodingNatBool
  exact congrComputes (ifComputes ((pairComputes i j).andThen Endpoints.equalComputes)
    (constantComputes _ encodingNatBool 1) (constantComputes _ encodingNatBool 0))
      (fun p => by simp only [Function.comp_apply,id_eq,decide_eq_true_eq])

def hit : Executes hitEncoding NegativeCertificateMachine.exponentEncoding
    (fun p => RationalInputMachine.hit p.1 p.2) :=
  NegativeCertificateMachine.Lists.map hitEncoding encodingNatBool encodingNatBool
    ((Executes.ofComputes (Wiring.firstComputes encodingNatBool encodingNatBool)).comp range)
      (fun p i => if i=p.2 then 1 else 0) (Executes.ofComputes hitCell)

def tripleCell (a b c : ℕ) : Computes encodingNatBool encodingNatBool
    (fun i => (if i=a then 1 else 0)+(if i=b then 1 else 0)+(if i=c then 1 else 0)) :=
  (pairComputes ((pairComputes (indicator a) (indicator b)).andThen add) (indicator c)).andThen add

def triple (a b c : ℕ) : Executes encodingNatBool NegativeCertificateMachine.exponentEncoding
    (fun n => RationalInputMachine.triple n a b c) :=
  range.comp (Executes.ofComputes (WireLists.mapComputes encodingNatBool encodingNatBool _ (tripleCell a b c)))
end
end Programs

namespace Access
noncomputable section
def «variables» : Computes encoding encodingNatBool Input.variables :=
  recode (Wiring.firstComputes encodingNatBool tailEncoding) Input.wire (fun _ => rfl) (fun _ => rfl)
def tail : Computes encoding tailEncoding (fun r => (r.original,r.body,r.addresses)) :=
  recode (Wiring.secondComputes encodingNatBool tailEncoding) Input.wire (fun _ => rfl) (fun _ => rfl)
def original : Computes encoding CommonFieldMachine.rootsEncoding Input.original :=
  tail.andThen (Wiring.firstComputes CommonFieldMachine.rootsEncoding lastEncoding)
def last : Computes encoding lastEncoding (fun r => (r.body,r.addresses)) :=
  tail.andThen (Wiring.secondComputes CommonFieldMachine.rootsEncoding lastEncoding)
def body : Computes encoding bodyEncoding Input.body := last.andThen (Wiring.firstComputes bodyEncoding addressesEncoding)
def addresses : Computes encoding addressesEncoding Input.addresses :=
  last.andThen (Wiring.secondComputes bodyEncoding addressesEncoding)
def count : Computes encoding encodingNatBool (fun r => r.original.length) :=
  (original.andThen (WireLists.lengthComputes ComplexIsolation.CertificateMachine.rootEncoding)).andThen UnaryBinary.computes
def negative : Computes encoding encodingNatBool (fun r => r.original.length+1) := count.andThen Programs.successor
def coefficients : Computes encoding CommonFieldMachine.coordinatesEncoding
    (fun r => RationalInputMachine.coefficients r.body) := body.andThen Programs.coefficients
end
end Access

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
