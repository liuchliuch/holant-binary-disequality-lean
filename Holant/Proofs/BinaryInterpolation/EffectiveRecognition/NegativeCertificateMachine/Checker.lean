import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.RootBridge


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open CommonFieldMachine (Executes)

def check (r : Input) : Bool := r.shape &&
  (decide (r.field.box=RationalBox.ofRectangle r.certificate.rectangle) &&
    (r.certificate.check (RootBridge.relationCode r.field.relation) &&
      (CommonFieldMachine.check r.field &&
        zeroCoefficients r.field.relation.length (DefectProgram.value r))))

noncomputable def executes : Executes encoding encodingBoolBool check := by
  let conjunction := fun {f g : Input → Bool} (a : Executes encoding encodingBoolBool f)
      (b : Executes encoding encodingBoolBool g) =>
    (Executes.pair a b).comp (Executes.ofComputes
      (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 && p.2)))
  let common := (Executes.ofComputes Access.field).comp CommonFieldMachine.FamilyMachine.executes
  exact conjunction (Executes.ofComputes Access.shape)
    (conjunction (Executes.ofComputes RootBridge.boxEqual)
      (conjunction RootBridge.rootExecutes (conjunction common DefectProgram.zeroExecutes)))

theorem check_fromCandidate {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (r : NullstellensatzSearch.Candidate m n S.length) :
    check (fromCandidate target S r) = NullstellensatzSearch.check target S r := by
  rw [check,fromCandidate_shape,Bool.true_and]
  change (decide (r.2.source=RationalBox.ofRectangle r.2.certificate.rectangle) &&
    (r.2.certificate.check (RootBridge.relationCode (List.ofFn r.2.relation)) &&
      (CommonFieldMachine.check (CommonFieldMachine.fromFamily r.2.relation r.2.source r.2.expression target) &&
        zeroCoefficients (List.ofFn r.2.relation).length
          (defect n (List.ofFn r.2.relation) (List.ofFn r.2.expression) (systemWire S)
            (List.ofFn (fun i => polyWire (r.2.multiplier i))))))) = _
  rw [CommonFieldMachine.check_fromFamily,RootBridge.relationCode_ofFn,
    List.length_ofFn,defect_wire,zeroCoefficients_wire]
  rfl

/-- Uniform byte output for the exact ORIGINAL target/equation/candidate data. -/
noncomputable def source_outputs {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (r : NullstellensatzSearch.Candidate m n S.length) :
    Turing.TM2OutputsInTime executes.machine.computer (encoding.encode (fromCandidate target S r))
      (some (encodingBoolBool.encode (NullstellensatzSearch.check target S r)))
      (executes.cost (fromCandidate target S r)) := by
  simpa only [check_fromCandidate] using executes.outputs (fromCandidate target S r)

theorem source_accept_sound {m n : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i,(target i).Represents (w i)) (S : EncodedSystem.System m n)
    (r : NullstellensatzSearch.Candidate m n S.length)
    (h : check (fromCandidate target S r)=true) :
    ¬ ∃ x : Fin n → ℂ, ∀ e∈S, MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  rw [check_fromCandidate] at h
  exact NullstellensatzSearch.check_sound target w ht S r h

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine
