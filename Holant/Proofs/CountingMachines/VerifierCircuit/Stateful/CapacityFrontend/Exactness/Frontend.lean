import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Exactness.Hold

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

The original-input-only frontend is identified with the existing compiler's
exact circuit encoding. The positive-round case consumes the previous wire
reset/repetition theorem; no second compiler or changed machine is introduced.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness

open Holant.LocalDrafts.CountingHardness

open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BitLayout OutputMachine
open scoped Classical

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)
local instance : ∀ k, Fintype (w.verifier.tm.Γ k) := w.verifier.finiteAlphabets

theorem canonical_eq (a : α) : Frontend.canonical w a =
    (addresses w.verifier.tm (capacity w (ea.encode a))).map
      (Reset.references w.verifier.tm (capacity w (ea.encode a))) := by
  unfold Frontend.canonical
  rw [← addresses_length]
  exact canonical_pack w.verifier.tm (capacity w (ea.encode a))

theorem first_eq (a : α) : Frontend.first w a =
    PrimitiveMachines.packedResult w.verifier.tm (capacity w (ea.encode a))
      (StatementRows.hold w.verifier.tm (capacity w (ea.encode a))
        (InitialRows.initialResult w (ea.encode a)).2) :=
  hold_eq w.verifier.tm (capacity w (ea.encode a)) (InitialRows.initialResult w (ea.encode a)).2

theorem steady_eq (a : α) : Frontend.steady w a =
    PrimitiveMachines.packedResult w.verifier.tm (capacity w (ea.encode a))
      (StatementRows.hold w.verifier.tm (capacity w (ea.encode a))
        (Reset.references w.verifier.tm (capacity w (ea.encode a)))) := by
  unfold Frontend.steady
  rw [canonical_eq]
  exact hold_eq w.verifier.tm (capacity w (ea.encode a)) _

theorem canonical_output (a : α) :
    (Frontend.canonical w a).getD (Frontend.acceptanceIndex w a) 0 =
      Reset.references w.verifier.tm (capacity w (ea.encode a)) (acceptance w (ea.encode a)) := by
  rw [canonical_eq]
  exact Layout.read_cell w.verifier.tm (capacity w (ea.encode a))
    (Reset.references w.verifier.tm (capacity w (ea.encode a))) w.verifier.tm.k₁ 0
    (some (w.verifier.outputAlphabet.symm (.inr true))) 0

theorem rawAssembly_succ (a : α) (T : ℕ) (hT : VerifierRun.horizon w a = T + 1) :
    Frontend.rawAssembly w a = Bounds.assemblyInput (compile w a) := by
  have hc := InitialRows.code_succ w (ea.encode a) T hT
  have hcode : (compile w a).circuit.code = InitialRows.code w (ea.encode a) :=
    InitialRows.compileWord_code w (ea.encode a)
  unfold Frontend.rawAssembly Bounds.assemblyInput
  rw [hT, if_neg (by omega), hcode, hc, compile_inputs, first_eq, steady_eq, canonical_output]
  simp [Frontend.initialData, PrimitiveMachines.packedResult, driverBytes, repeatBytes,
    rowBytes_append, rowBytes_replicate, Reset.steadyRows, List.append_assoc]

/-- No hold, assembly, correctness or time premise is supplied by the caller. -/
theorem rawAssembly_eq (a : α) :
    Frontend.rawAssembly w a = Bounds.assemblyInput (compile w a) := by
  cases h : VerifierRun.horizon w a with
  | zero => exact Frontend.zero_assembly w a h
  | succ T => exact rawAssembly_succ w a T h

def assemblyComputes : Computes ea assemblyEncoding (fun a => Bounds.assemblyInput (compile w a)) :=
  congrComputes (Frontend.rawAssemblyComputes w) (rawAssembly_eq w)

theorem rawBytes_eq (a : α) :
    assembleBytes (Frontend.rawAssembly w a) = CircuitInstance.encoding.encode (compile w a) := by
  rw [rawAssembly_eq]
  exact assemble_eq_encoding (compile w a)

/-- Same program as the delivered rawBytesComputes, now with the exact original
CircuitInstance encoding as its proved output specification. -/
def computes : Computes ea CircuitInstance.encoding (compile w) :=
  recode (Frontend.rawBytesComputes w) id (fun _ => rfl) (rawBytes_eq w)

theorem machine_unchanged : (computes w).machine = (Frontend.rawBytesComputes w).machine := rfl
theorem time_unchanged : (computes w).time = (Frontend.rawBytesComputes w).time := rfl
set_option backward.isDefEq.respectTransparency true in
theorem assembly_machine_unchanged :
    (assemblyComputes w).machine = (Frontend.rawAssemblyComputes w).machine := by
  simp only [assemblyComputes, congrComputes, recode]

def outputs (a : α) :
    TM2OutputsInTime (Frontend.rawBytesComputes w).machine.computer (ea.encode a)
      (some (CircuitInstance.encoding.encode (compile w a)))
      ((Frontend.rawBytesComputes w).time.eval (ea.encode a).length) :=
  (computes w).outputs a

theorem original_primitive_bound (a : α) :
    primitiveCost (computes w).machine ((computes w).outputs a).steps
      (some (initList (computes w).machine.computer (ea.encode a))) ≤
        (primitivePolynomial (computes w)).eval (ea.encode a).length :=
  computes_primitive_cost (computes w) a

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness
