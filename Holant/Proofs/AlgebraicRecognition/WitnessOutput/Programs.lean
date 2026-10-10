import Holant.Proofs.AlgebraicRecognition.WitnessOutput.Codec


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes coordinatesEncoding)
open PositiveCertificateMachine ComplexIsolation
open Holant.LocalDrafts.MainChain.TransformRecognition

def accepted (r : Request) : List Output :=
  if PositiveCertificateMachine.check r then [emit r] else []
def scan (rs : List Request) : List Output := rs.flatMap accepted

theorem mem_accepted {r : Request} {o : Output} :
    o ∈ accepted r ↔ PositiveCertificateMachine.check r = true ∧ o = emit r := by
  cases h : PositiveCertificateMachine.check r <;> simp [accepted, h, eq_comm]

theorem mem_scan {rs : List Request} {o : Output} :
    o ∈ scan rs ↔ ∃ r ∈ rs, PositiveCertificateMachine.check r = true ∧ o = emit r := by
  simp only [scan, List.mem_flatMap, mem_accepted]

noncomputable section

def matrixEntryComputes (u v : Bool) : Computes requestEncoding coordinatesEncoding
    (fun r => matrixEntry r u v) :=
  AccessPrograms.get coordinatesEncoding [] valuesComputes
    (constantComputes requestEncoding UnaryBinary.unaryEncoding (MatrixWitness.index u v).val)

def matrixComputes : Computes requestEncoding quadEncoding (fun r => quad (matrixEntry r)) :=
  pairComputes (pairComputes (matrixEntryComputes false false) (matrixEntryComputes false true))
    (pairComputes (matrixEntryComputes true false) (matrixEntryComputes true true))

def adjugateEntryComputes (u v : Bool) : Computes requestEncoding coordinatesEncoding
    (fun r => adjugateEntry r u v) := by
  by_cases huv : u = v
  · simpa only [adjugateEntry, if_pos huv] using matrixEntryComputes (!u) (!v)
  · let neg := (pairComputes (constantComputes requestEncoding rationalEncoding (-1))
      (matrixEntryComputes u v)).andThen CommonFieldMachine.CoordinatePrimitives.scale
    simpa only [adjugateEntry, if_neg huv, Function.comp_def] using neg

def inverseEntryExecutes (u v : Bool) : Executes requestEncoding coordinatesEncoding
    (fun r => inverseEntry r u v) :=
  ((Executes.ofComputes relationComputes).pair
    ((Executes.ofComputes (AccessPrograms.get coordinatesEncoding [] valuesComputes
      (constantComputes requestEncoding UnaryBinary.unaryEncoding 4))).pair
        (Executes.ofComputes (adjugateEntryComputes u v)))).comp CommonFieldMachine.Multiplication.mul

def inverseExecutes : Executes requestEncoding quadEncoding (fun r => quad (inverseEntry r)) :=
  ((inverseEntryExecutes false false).pair (inverseEntryExecutes false true)).pair
    ((inverseEntryExecutes true false).pair (inverseEntryExecutes true true))

def rootComputes : Computes requestEncoding CertificateMachine.rootEncoding
    (fun r => r.certificate.rootCode (relationPolynomial r.family.relation)) :=
  (pairComputes (relationComputes.andThen relationPolynomialComputes) certificateComputes).andThen
    CertificateMachine.rootComputes

/-- The binary difference is converted by the delivered real program, then
the unary range and each shifted lookup are physically executed. -/
def scalarValuesExecutes : Executes requestEncoding vectorsEncoding scalarValues := by
  let length := (valuesComputes.andThen (WireLists.lengthComputes coordinatesEncoding)).andThen
    UnaryBinary.computes
  let count := (pairComputes length (constantComputes requestEncoding encodingNatBool 5)).andThen
    Endpoints.subtractComputes
  let convert := RootSearchDriver.Height.binaryToUnary
  let unary : Executes encodingNatBool UnaryBinary.unaryEncoding id :=
    ⟨convert.machine, fun n => convert.time (encodingNatBool.encode n).length, convert.outputs⟩
  let indices := ((Executes.ofComputes count).comp unary).comp
    (Executes.ofComputes ComponentSelection.UnaryRange.computes)
  let cellEncoding := pairEncoding requestEncoding UnaryBinary.unaryEncoding
  let r := Wiring.firstComputes requestEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes requestEncoding UnaryBinary.unaryEncoding
  let shifted := (pairComputes (constantComputes cellEncoding UnaryBinary.unaryEncoding 5) i).andThen
    AccessPrograms.unaryAdd
  let cell := AccessPrograms.get coordinatesEncoding [] (r.andThen valuesComputes) shifted
  exact ((Executes.ofComputes (identityComputes requestEncoding)).pair indices).comp
    (Executes.mapList requestEncoding UnaryBinary.unaryEncoding coordinatesEncoding
      (fun r i => r.values.getD (5+i) []) (Executes.ofComputes cell))

def emitExecutes : Executes requestEncoding outputEncoding emit := by
  let raw := (Executes.ofComputes rootComputes).pair
    ((Executes.ofComputes relationComputes).pair
      ((Executes.ofComputes matrixComputes).pair
        (inverseExecutes.pair (scalarValuesExecutes.pair (Executes.ofComputes valuesComputes)))))
  exact Executes.recode raw id (fun _ => rfl) (fun _ => rfl)

def selectAcceptedComputes : Computes (pairEncoding encodingBoolBool outputEncoding)
    outputsEncoding (fun p => if p.1 then [p.2] else []) :=
  ifComputes (Wiring.firstComputes encodingBoolBool outputEncoding)
    (fixedListComputes (pairEncoding encodingBoolBool outputEncoding) outputEncoding
      (fun p (_ : Unit) => p.2) (fun _ => Wiring.secondComputes encodingBoolBool outputEncoding) [()])
    (constantComputes (pairEncoding encodingBoolBool outputEncoding) outputsEncoding [])

def acceptedExecutes : Executes requestEncoding outputsEncoding accepted :=
  (PositiveCertificateMachine.executes.pair emitExecutes).comp
    (Executes.ofComputes selectAcceptedComputes)

/-- This is an actual all-candidate scan in catalogue order. Failed candidates
also incur the extraction cost: the selection program computes both branches. -/
def scanExecutes : Executes (framedListEncoding requestEncoding) outputsEncoding scan := by
  let prepare := Executes.ofComputes (pairComputes
    (constantComputes (framedListEncoding requestEncoding) encodingNatBool 0)
    (identityComputes (framedListEncoding requestEncoding)))
  let cell := (Executes.ofComputes (Wiring.secondComputes encodingNatBool requestEncoding)).comp
    acceptedExecutes
  let mapped := Executes.mapList encodingNatBool requestEncoding outputsEncoding
    (fun _ r => accepted r) cell
  exact ((prepare.comp mapped).comp (Executes.ofComputes (WireLists.flatten outputEncoding))).congr
    (fun rs => by rfl)

def someComputes : Computes outputEncoding resultEncoding (fun o => some o) :=
  recode (joinComputes (constantComputes outputEncoding Frame.wordEncoding [true])
    (encodeComputes outputEncoding)) id (fun _ => rfl) (fun _ => rfl)

/-- Only a typed, faithful list word is claimed. Option tagging, the scan and
the default none lookup are real programs; no malformed-word decoder is used. -/
def headComputes : Computes outputsEncoding resultEncoding List.head? := by
  let tagged := WireLists.mapComputes outputEncoding resultEncoding (fun o => some o) someComputes
  let first := tagged.andThen (getDComputes resultEncoding 0 none)
  exact congrComputes first (fun os => by cases os <;> rfl)

def emit_outputs (r : Request) : TM2OutputsInTime emitExecutes.machine.computer
    (requestEncoding.encode r) (some (outputEncoding.encode (emit r))) (emitExecutes.cost r) :=
  emitExecutes.outputs r

def source_outputs {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    TM2OutputsInTime emitExecutes.machine.computer (requestEncoding.encode (fromSource target S a))
      (some (outputEncoding.encode (ofCandidate a))) (emitExecutes.cost (fromSource target S a)) := by
  simpa only [emit_fromSource] using emitExecutes.outputs (fromSource target S a)

theorem emission_primitives (r : Request) :
    primitiveCost emitExecutes.machine (emitExecutes.outputs r).steps
      (some (initList emitExecutes.machine.computer (requestEncoding.encode r))) ≤
      emitExecutes.cost r * emitExecutes.machine.primitiveBudget := emitExecutes.primitive_bound r

theorem emission_prefix_bits (r : Request) {i : ℕ}
    (hi : i ≤ (emitExecutes.outputs r).steps) {c : emitExecutes.machine.Config}
    (hc : (fun s => s.bind emitExecutes.machine.computer.step)^[i]
      (some (initList emitExecutes.machine.computer (requestEncoding.encode r))) = some c) :
    stackSize c.stk ≤ (requestEncoding.encode r).length +
      emitExecutes.cost r * emitExecutes.machine.primitiveBudget := by
  have h := emitExecutes.machine.run_size_le _ c i hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (hi.trans (emitExecutes.outputs r).steps_le_m)) _)

end
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput
