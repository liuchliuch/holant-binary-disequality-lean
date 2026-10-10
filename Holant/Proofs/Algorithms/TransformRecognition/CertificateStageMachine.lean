import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.API
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Resources
import Holant.Proofs.Tractability.AffineMachine.ResidueCells
import Holant.Proofs.Algorithms.TransformRecognition.StructuredDovetail


namespace Holant.LocalDrafts.MainChain.TransformRecognition.CertificateStageMachine
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev Input := List PositiveCertificateMachine.Request × List NegativeCertificateMachine.Input
def positiveEncoding := framedListEncoding PositiveCertificateMachine.requestEncoding
def negativeEncoding := framedListEncoding NegativeCertificateMachine.encoding
def encoding : Encoding Input Bool := pairEncoding positiveEncoding negativeEncoding
def resultEncoding := optionEncoding encodingBoolBool

def choose (p : Bool × Bool) : Option Bool :=
  if p.1 then some true else if p.2 then some false else none
def value (r : Input) : Option Bool := choose (r.1.any PositiveCertificateMachine.check,r.2.any NegativeCertificateMachine.check)

noncomputable section

/-- Instantiated below with the actual positive and negative programs. The
dummy natural context is copied by real tape programs, not a free host map. -/
def checkList {A : Type} (ea : Encoding A Bool) (f : A → Bool)
    (w : Executes ea encodingBoolBool f) :
    Executes (framedListEncoding ea) encodingBoolBool (fun xs => xs.any f) := by
  let prepare := Executes.ofComputes (pairComputes
    (constantComputes (framedListEncoding ea) encodingNatBool 0)
    (identityComputes (framedListEncoding ea)))
  let cell := (Executes.ofComputes (Wiring.secondComputes encodingNatBool ea)).comp w
  let mapped := Executes.mapList encodingNatBool ea encodingBoolBool (fun _ a => f a) cell
  let folded := (prepare.comp mapped).comp
    (Executes.ofComputes Holant.LocalDrafts.Tractability.AffineMachine.ResidueCells.any)
  exact folded.congr (fun xs => by simp only [List.any_map,Function.comp_def,id_eq])

def chooseComputes : Computes (pairEncoding encodingBoolBool encodingBoolBool)
    resultEncoding choose :=
  FiniteRecode.computes _ _ choose 4 (fun p => by rcases p with ⟨a,b⟩; cases a <;> cases b <;> decide)

def executes : Executes encoding resultEncoding value := by
  let positive := (Executes.ofComputes (Wiring.firstComputes positiveEncoding negativeEncoding)).comp
    (checkList PositiveCertificateMachine.requestEncoding PositiveCertificateMachine.check PositiveCertificateMachine.executes)
  let negative := (Executes.ofComputes (Wiring.secondComputes positiveEncoding negativeEncoding)).comp
    (checkList NegativeCertificateMachine.encoding NegativeCertificateMachine.check NegativeCertificateMachine.executes)
  exact (positive.pair negative).comp (Executes.ofComputes chooseComputes)

end

/-- Mathematical description of generated canonical bytes, NOT an assumed
input generator. The physical catalogue workers/root must implement this map
before this stage can be called from the original input. -/
def fromHeight {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) : Input :=
  ((StructuredCatalogue.positive m k h).map (PositiveCertificateMachine.fromSource target S),
   (StructuredCatalogue.negative m (5+k) S.length h).map (NegativeCertificateMachine.fromCandidate target S))

theorem value_fromHeight {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    value (fromHeight target S h)=StructuredDovetail.stage target S h := by
  simp only [value,fromHeight,List.any_map,Function.comp_def,PositiveCertificateMachine.check_fromSource,
    NegativeCertificateMachine.check_fromCandidate,choose,StructuredDovetail.stage,StructuredDovetail.positive,
    StructuredDovetail.negative]
  rfl

noncomputable def source_outputs {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    TM2OutputsInTime executes.machine.computer (encoding.encode (fromHeight target S h))
      (some (resultEncoding.encode (StructuredDovetail.stage target S h)))
      (executes.cost (fromHeight target S h)) := by
  simpa only [value_fromHeight] using executes.outputs (fromHeight target S h)

theorem source_true_sound {m k : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (hw : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (ha : value (fromHeight target S h)=some true) :
    ∃ z : Fin (5+k) → ℂ, ∀ e ∈ S, MvPolynomial.aeval z (EncodedSystem.polynomial w e)=0 :=
  StructuredDovetail.true_sound target w hw S h ((value_fromHeight target S h).symm.trans ha)

theorem source_false_sound {m k : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (hw : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m (5+k)) (h : ℕ)
    (ha : value (fromHeight target S h)=some false) :
    ¬∃ z : Fin (5+k) → ℂ, ∀ e ∈ S, MvPolynomial.aeval z (EncodedSystem.polynomial w e)=0 :=
  StructuredDovetail.false_sound target w hw S h ((value_fromHeight target S h).symm.trans ha)

end Holant.LocalDrafts.MainChain.TransformRecognition.CertificateStageMachine
