import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Exactness.Frontend
import Holant.Proofs.CountingMachines.CircuitNative.CircuitSize
import Holant.Complexity.OracleOneQuery.Reduction

set_option backward.isDefEq.respectTransparency false

/-!
Ported reference proof. See the task validation reports.

The actual verifier-to-NAND one-query reduction, after exact emitted bytes have
been identified. Its only verifier input is the existing SharpPWitness. The
query compiler, natural-answer copier and answer-size bound are all concrete.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness


open Computability Holant.Complexity BinaryCompose

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

theorem witness_slots (a : α) : (compile w a).inputs = w.witnessLength.eval (ea.encode a).length := rfl

theorem unique_extension (a : α) (bits : Fin (compile w a).inputs → Bool) :
    ∃! gates : Fin (compile w a).circuit.gates → Bool,
      (compile w a).circuit.consistent bits gates = true := by
  refine ⟨(compile w a).circuit.trace bits, ?_, ?_⟩
  · exact (Circuit.consistent_iff _ _ _).mpr rfl
  · intro gates hg
    exact (Circuit.consistent_iff _ _ _).mp hg

theorem preserves_count (a : α) : CircuitInstance.value (compile w a) = f a := compile_count w a

theorem preserves_extended_count (a : α) :
    countAccepted (fun xz : (Fin (compile w a).inputs → Bool) ×
      (Fin (compile w a).circuit.gates → Bool) =>
        (compile w a).circuit.accepts xz.1 xz.2) = f a := compile_count_extensions w a

/-- One physical query to the existing CircuitInstance value problem. The
oracle answer length is bounded by CircuitInstance.outputBound, so copying its
binary natural answer is included in the reduction's actual time polynomial. -/
def reduction : PolyTimeOracleReduction ea encodingNatBool CircuitInstance.encoding encodingNatBool
    f CircuitInstance.value :=
  OracleOneQuery.of_eq (computes w) (identityComputes encodingNatBool)
    CircuitInstance.outputBound f (fun a => (compile_count w a).symm)

include w in
theorem reducible : OracleReducible ea encodingNatBool CircuitInstance.encoding encodingNatBool
    f CircuitInstance.value := ⟨reduction w⟩

/-- Represented SharpP membership supplies an actual verifier witness, not a
correctness/time assumption about the compiler constructed above. -/
theorem sharpP_reducible (h : InSharpP ea f) :
    OracleReducible ea encodingNatBool CircuitInstance.encoding encodingNatBool f CircuitInstance.value := by
  rcases h with ⟨w⟩
  exact reducible w

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Exactness
