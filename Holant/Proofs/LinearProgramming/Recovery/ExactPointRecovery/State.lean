import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.Request
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.Denominator
import Holant.Proofs.LinearProgramming.Foundation.Infrastructure.Arithmetic

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
A scalar recovery state stores original Input/coordinate, binary dyadic
numerator/denominator, and binary remaining rounds. Every update consults
the Boolean parsed from the real Receipt of the emitted midpoint request.
There is no point-valued oracle, host inverse, or runtime existential choice.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators Codec
noncomputable section

abbrev Payload := CoordinateQuery × (ℕ × ℕ)
def payloadEncoding := Request.encoding
abbrev State := ℕ × Payload
def encoding := pairEncoding encodingNatBool payloadEncoding
def bodyEncoding := pairEncoding encodingBoolBool encoding
def remaining (s : State) : ℕ := s.1
def payload (s : State) : Payload := s.2
def coordinate (v : Payload) : CoordinateQuery := v.1
def numerator (v : Payload) : ℕ := v.2.1
def denominator (v : Payload) : ℕ := v.2.2
def stamp (r : ℕ) (v : Payload) : State := (r,v)
def midpoint (v : Payload) : Request.Query := (coordinate v,2*numerator v+1,2*denominator v)
def response (v : Payload) : Request.Data := Request.value (midpoint v)
def accepted (v : Payload) : Bool := (response v).1
def advance (v : Payload) : Payload :=
  (coordinate v,if accepted v then 2*numerator v else 2*numerator v+1,2*denominator v)
def payloadAt (c : CoordinateQuery) : ℕ → Payload
  | 0 => (c,0,1)
  | k+1 => advance (payloadAt c k)
def initial (c : CoordinateQuery) : State := stamp (Denominator.rounds c.1.val) (payloadAt c 0)
def finish : ℕ → Payload → State
  | 0,v => stamp 0 v
  | r+1,v => finish r (advance v)
def resultState (c : CoordinateQuery) : State := finish (Denominator.rounds c.1.val) (payloadAt c 0)
def interval (v : Payload) : ℚ × ℚ :=
  ((numerator v:ℚ)/denominator v,((numerator v:ℚ)+1)/denominator v)

def counterComputes : Computes encoding encodingNatBool remaining := Wiring.firstComputes _ _
def payloadComputes : Computes encoding payloadEncoding payload := Wiring.secondComputes _ _
def coordinateComputes : Computes payloadEncoding coordinateEncoding coordinate := Wiring.firstComputes _ _
def fractionComputes : Computes payloadEncoding ThresholdProgram.fractionEncoding (fun v : Payload => v.2) :=
  Wiring.secondComputes _ _
def numeratorComputes : Computes payloadEncoding encodingNatBool numerator :=
  fractionComputes.andThen (Wiring.firstComputes _ _)
def denominatorComputes : Computes payloadEncoding encodingNatBool denominator :=
  fractionComputes.andThen (Wiring.secondComputes _ _)
def doubledNumerator : Computes payloadEncoding encodingNatBool (fun v : Payload => 2*numerator v) :=
  congrComputes ((pairComputes numeratorComputes numeratorComputes).andThen
    Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.addComputes)
    (fun v => by change numerator v + numerator v = 2*numerator v; omega)
def middleNumerator : Computes payloadEncoding encodingNatBool (fun v : Payload => 2*numerator v+1) :=
  (pairComputes doubledNumerator (constantComputes payloadEncoding encodingNatBool 1)).andThen
    Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.addComputes
def doubledDenominator : Computes payloadEncoding encodingNatBool (fun v : Payload => 2*denominator v) :=
  congrComputes ((pairComputes denominatorComputes denominatorComputes).andThen
    Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.addComputes)
    (fun v => by change denominator v + denominator v = 2*denominator v; omega)
def midpointComputes : Computes payloadEncoding Request.encoding midpoint :=
  pairComputes coordinateComputes (pairComputes middleNumerator doubledDenominator)
def responseComputes : Computes payloadEncoding Request.dataEncoding response :=
  midpointComputes.andThen Request.computes
def acceptedComputes : Computes payloadEncoding encodingBoolBool accepted :=
  responseComputes.andThen (Wiring.firstComputes encodingBoolBool Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.StepProgram.encoding)
def advanceComputes : Computes payloadEncoding payloadEncoding advance :=
  pairComputes coordinateComputes (pairComputes
    (ifComputes acceptedComputes doubledNumerator middleNumerator) doubledDenominator)
def countBinary : Computes coordinateEncoding encodingNatBool (fun c : CoordinateQuery => Denominator.rounds c.1.val) :=
  Denominator.countComputes.andThen UnaryBinary.computes
def initialPayloadComputes : Computes coordinateEncoding payloadEncoding (fun c => payloadAt c 0) :=
  pairComputes (identityComputes coordinateEncoding)
    (pairComputes (constantComputes coordinateEncoding encodingNatBool 0)
      (constantComputes coordinateEncoding encodingNatBool 1))
def prepare : Computes coordinateEncoding encoding initial := pairComputes countBinary initialPayloadComputes

@[simp] theorem payloadAt_coordinate (c : CoordinateQuery) (k : ℕ) : coordinate (payloadAt c k)=c := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih
@[simp] theorem payloadAt_denominator (c : CoordinateQuery) (k : ℕ) : denominator (payloadAt c k)=2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [payloadAt,advance,denominator,ih,pow_succ,Nat.mul_comm]
theorem payloadAt_numerator (c : CoordinateQuery) (k : ℕ) : numerator (payloadAt c k)<2^k := by
  induction k with
  | zero => simp [payloadAt,numerator]
  | succ k ih =>
    have hp : 0<2^k := by positivity
    simp only [numerator] at ih
    simp only [payloadAt,advance,numerator,pow_succ]
    split_ifs <;> omega
theorem finish_exact (c : CoordinateQuery) (k r : ℕ) :
    finish r (payloadAt c k)=stamp 0 (payloadAt c (k+r)) := by
  induction r generalizing k with
  | zero => simp [finish,stamp]
  | succ r ih =>
    change finish r (payloadAt c (k+1))=_
    rw [ih]
    congr 2
    omega
@[simp] theorem result_exact (c : CoordinateQuery) :
    resultState c=stamp 0 (payloadAt c (Denominator.rounds c.1.val)) := by
  simpa [resultState] using finish_exact c 0 (Denominator.rounds c.1.val)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
