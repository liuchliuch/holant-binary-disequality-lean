import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Checker


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler

def emit (x : Input) : Option RootCode :=
  if check x then some (x.2.rootCode x.1) else none

theorem emit_sound {x : Input} {c : RootCode} (h : emit x = some c) :
    ∃ z : ℂ, c.Represents z := by
  unfold emit at h
  split at h
  · have hc : x.2.rootCode x.1 = c := Option.some.inj h
    subst c
    have ht : check x = true := by assumption
    exact Certificate.check_sound ((check_eq x).symm.trans ht)
  · simp at h

noncomputable section
def rectangleComputes : Computes certificateEncoding rectangleEncoding Certificate.rectangle := by
  let re := Scalars.real centerComputes
  let im := Scalars.imag centerComputes
  let w := pairComputes (pairComputes (Scalars.sub re radiusComputes) (Scalars.add re radiusComputes))
    (pairComputes (Scalars.sub im radiusComputes) (Scalars.add im radiusComputes))
  exact recode w id (fun _ => rfl) (fun _ => rfl)

def rootComputes : Computes inputEncoding rootEncoding (fun x : Input => x.2.rootCode x.1) :=
  recode (pairComputes inputPolynomial (inputCertificate.andThen rectangleComputes))
    id (fun _ => rfl) (fun _ => rfl)

def someComputes : Computes rootEncoding resultEncoding (fun c => some c) :=
  recode (joinComputes (constantComputes rootEncoding Frame.wordEncoding [true])
    (encodeComputes rootEncoding)) id (fun _ => rfl) (fun _ => rfl)

def selectOutput : Computes (pairEncoding encodingBoolBool rootEncoding) resultEncoding
    (fun x : Bool × RootCode => if x.1 then some x.2 else none) :=
  ifComputes (Wiring.firstComputes encodingBoolBool rootEncoding)
    ((Wiring.secondComputes encodingBoolBool rootEncoding).andThen someComputes)
    (constantComputes (pairEncoding encodingBoolBool rootEncoding) resultEncoding none)

/-- Root existence enters only in emit_sound AFTER the exact Boolean checker;
the program returns bytes, never a semantic complex number. -/
def emitComputes : FiniteComputes inputEncoding resultEncoding emit :=
  ((computes.pair (FiniteComputes.ofPoly rootComputes)).andThen
    (FiniteComputes.ofPoly selectOutput)).congr (fun x => by simp only [Function.comp_apply, emit, check_eq])

def checker_outputs (x : Input) :
    TM2OutputsInTime computes.machine.computer (inputEncoding.encode x)
      (some (encodingBoolBool.encode (x.2.check x.1)))
      (computes.time (inputEncoding.encode x).length) := computes.outputs x

def emitter_outputs (x : Input) :
    TM2OutputsInTime emitComputes.machine.computer (inputEncoding.encode x)
      (some (resultEncoding.encode (emit x)))
      (emitComputes.time (inputEncoding.encode x).length) := emitComputes.outputs x

def checkerTimed : Turing.TM2ComputableInTime inputEncoding.encode encodingBoolBool.encode
    (fun x : Input => x.2.check x.1) := computes.toTM2ComputableInTime

def emitterTimed : Turing.TM2ComputableInTime inputEncoding.encode resultEncoding.encode emit :=
  emitComputes.toTM2ComputableInTime

theorem accepted_decoding_sound (x : Input) (c : RootCode)
    (h : resultEncoding.decode (resultEncoding.encode (emit x)) = some (some c)) :
    ∃ z : ℂ, c.Represents z := by
  rw [resultEncoding.decode_encode] at h
  exact emit_sound (Option.some.inj h)

theorem checker_intermediate_bits (x : Input) {i : ℕ}
    (hi : i ≤ computes.time (inputEncoding.encode x).length) {c : computes.machine.Config}
    (hc : (fun s => s.bind computes.machine.computer.step)^[i]
      (some (initList computes.machine.computer (inputEncoding.encode x))) = some c) :
    stackSize c.stk ≤ computes.width (inputEncoding.encode x).length :=
  computes.intermediate_bits x hi hc

theorem emitter_intermediate_bits (x : Input) {i : ℕ}
    (hi : i ≤ emitComputes.time (inputEncoding.encode x).length) {c : emitComputes.machine.Config}
    (hc : (fun s => s.bind emitComputes.machine.computer.step)^[i]
      (some (initList emitComputes.machine.computer (inputEncoding.encode x))) = some c) :
    stackSize c.stk ≤ emitComputes.width (inputEncoding.encode x).length :=
  emitComputes.intermediate_bits x hi hc

theorem checker_primitive_bound (x : Input) :
    primitiveCost computes.machine (computes.outputs x).steps
      (some (initList computes.machine.computer (inputEncoding.encode x))) ≤
        computes.time (inputEncoding.encode x).length * computes.machine.primitiveBudget :=
  computes.primitive_bound x

theorem emitter_primitive_bound (x : Input) :
    primitiveCost emitComputes.machine (emitComputes.outputs x).steps
      (some (initList emitComputes.machine.computer (inputEncoding.encode x))) ≤
        emitComputes.time (inputEncoding.encode x).length * emitComputes.machine.primitiveBudget :=
  emitComputes.primitive_bound x

end
end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine
