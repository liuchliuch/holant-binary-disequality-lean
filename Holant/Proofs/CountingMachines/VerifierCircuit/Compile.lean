import Holant.Proofs.CountingMachines.VerifierCircuit.Initial

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# A fixed-verifier NAND circuit on exactly its witness wires

Ported reference proof. See the task validation reports.

`compileWord` takes only the original encoded word. Fixed truth-table choices
depend on the verifier, not on a run or witness. The following semantic proof
scripts do not establish a physical `BinaryCompose.Computes` witness.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit

open Holant.LocalDrafts.CountingHardness

open Turing Computability Holant.Complexity BitLayout
open scoped Classical

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

local instance compileAlphabets : ∀ k, Fintype (w.verifier.tm.Γ k) := w.verifier.finiteAlphabets

def capacity (word : List Bool) : ℕ :=
  (VerifierRun.capacityPolynomial w).eval word.length + VerifierRun.pushBudget w.verifier.tm

def acceptance (word : List Bool) : Address w.verifier.tm (capacity w word) :=
  cellAddr w.verifier.tm (capacity w word) w.verifier.tm.k₁ 0
    (some (w.verifier.outputAlphabet.symm (Sum.inr true)))

def body (word : List Bool) : Emit (Fin (w.witnessLength.eval word.length)) Unit :=
  Emit.seq (Initial.emit w.verifier.tm (capacity w word) w.verifier.inputAlphabet
    word (w.witnessLength.eval word.length))
    (Emit.seq (Unroll.emit w.verifier.tm (capacity w word)
      ((VerifierRun.horizonPolynomial w).eval word.length))
      (Emit.route (fun _ : Unit => acceptance w word)))

def compileWord (word : List Bool) : CircuitInstance :=
  ⟨w.witnessLength.eval word.length, Emit.finish (body w word) (fun i => i)⟩

def compile (a : α) : CircuitInstance := compileWord w (ea.encode a)

@[simp] theorem compile_inputs (a : α) : (compile w a).inputs = VerifierRun.witnessLength w a := rfl

theorem compileWord_eval (word : List Bool) (bits : Fin (w.witnessLength.eval word.length) → Bool) :
    (compileWord w word).circuit.eval bits =
      encode w.verifier.tm (capacity w word)
        (PackedStep.packRaw w.verifier.tm (capacity w word)
          ((VerifierRun.holdStep w.verifier.tm)^[(VerifierRun.horizonPolynomial w).eval word.length]
            (initList w.verifier.tm (Initial.inputWord w.verifier.tm w.verifier.inputAlphabet
              word (w.witnessLength.eval word.length) bits)))) (acceptance w word) := by
  change (Emit.finish (body w word) (fun i => i)).eval bits = _
  unfold body
  rw [Emit.finish_eval (Emit.seq_denotes
    (Initial.denotes w.verifier.tm (capacity w word) w.verifier.inputAlphabet word _)
    (Emit.seq_denotes (Unroll.denotes w.verifier.tm (capacity w word) _)
      (Emit.route_denotes (fun _ : Unit => acceptance w word))))]
  have hC : (Initial.inputWord w.verifier.tm w.verifier.inputAlphabet word
      (w.witnessLength.eval word.length) bits).length +
      (VerifierRun.horizonPolynomial w).eval word.length * VerifierRun.pushBudget w.verifier.tm +
      VerifierRun.pushBudget w.verifier.tm ≤ capacity w word + 1 := by
    simp [capacity, VerifierRun.capacityPolynomial]
  rw [Unroll.actual_run w.verifier.tm (capacity w word) _ _ hC _ (Nat.le_refl _)]

theorem initial_word_eq (a : α) (bits : Fin (VerifierRun.witnessLength w a) → Bool) :
    Initial.inputWord w.verifier.tm w.verifier.inputAlphabet (ea.encode a)
      (VerifierRun.witnessLength w a) bits = VerifierRun.inputWord w a bits := by
  simp [Initial.inputWord, Initial.tokens_map, VerifierRun.inputWord, encodingProd, encodingList]

theorem terminal_acceptance (word : List Bool) (b : Bool) :
    encode w.verifier.tm (capacity w word)
      (PackedStep.packRaw w.verifier.tm (capacity w word)
        (haltList w.verifier.tm [w.verifier.outputAlphabet.symm (Sum.inr b)]))
      (acceptance w word) = b := by
  have he := w.verifier.outputAlphabet.symm.injective
  cases b <;>
    simp [encode, PackedStep.packRaw, haltList, BoundedTableau.pad, acceptance,
      cellAddr, oneHot, he.eq_iff]

/-- No circuit, trajectory, or simulation-correctness premise is supplied. -/
theorem compile_eval (a : α) (bits : Fin (VerifierRun.witnessLength w a) → Bool) :
    (compile w a).circuit.eval bits = w.accept (a, List.ofFn bits) := by
  change (compileWord w (ea.encode a)).circuit.eval bits = _
  rw [compileWord_eval w (ea.encode a) bits]
  change encode w.verifier.tm (capacity w (ea.encode a))
    (PackedStep.packRaw w.verifier.tm (capacity w (ea.encode a))
      ((VerifierRun.holdStep w.verifier.tm)^[VerifierRun.horizon w a]
        (initList w.verifier.tm (Initial.inputWord w.verifier.tm w.verifier.inputAlphabet
          (ea.encode a) (VerifierRun.witnessLength w a) bits)))) (acceptance w (ea.encode a)) = _
  rw [initial_word_eq, VerifierRun.verifier_terminal, terminal_acceptance]

theorem compile_count (a : α) : CircuitInstance.value (compile w a) = f a := by
  rw [w.counts a]
  unfold CircuitInstance.value witnessCount
  congr 1
  funext bits
  exact compile_eval w a bits

/-- Internal gates have the unique extension already proved for `Circuit`;
there is no extra multiplicity for padded cells or early halting. -/
theorem compile_count_extensions (a : α) :
    countAccepted (fun xz : (Fin (compile w a).inputs → Bool) ×
      (Fin (compile w a).circuit.gates → Bool) =>
      (compile w a).circuit.accepts xz.1 xz.2) = f a := by
  rw [Circuit.parsimonious]
  exact compile_count w a

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit
