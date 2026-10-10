import Holant.Proofs.CountingMachines.VerifierCircuit.GateCost

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Polynomial gate bound in the original input length

Ported reference proof. See the task validation reports.

The initial data-dependent constants cost one gate; a witness-dependent cell
bit costs six. Every unrolled step has the same exact syntactic gate cost.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit

open Holant.LocalDrafts.CountingHardness

open Turing Computability Holant.Complexity BitLayout
open scoped Classical

namespace Initial

variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]
variable (e : tm.Γ tm.k₀ ≃ Bool ⊕ Bool) (word : List Bool) (W : ℕ)

def inputBitCost (i : Fin (C + 1)) : ℕ :=
  match (tokens word W)[i.val]? with
  | some (.inr _) => 6
  | _ => 1

theorem inputBit_adds (i : Fin (C + 1)) (a : Option (tm.Γ tm.k₀)) :
    Emit.Adds (inputBit tm C e word W i a) (inputBitCost C word W i) := by
  unfold inputBit inputBitCost
  cases h : (tokens word W)[i.val]? with
  | none => exact Emit.constant_adds _
  | some token =>
    cases token with
    | inl b => exact Emit.constant_adds _
    | inr j => exact boolMap_adds _ _

def bitCost : Address tm C → ℕ
  | .inr (.inr ⟨k, i, _⟩) => if k = tm.k₀ then inputBitCost C word W i else 1
  | _ => 1

theorem bit_adds (a : Address tm C) : Emit.Adds (bit tm C e word W a) (bitCost tm C word W a) := by
  cases a with
  | inl l => exact Emit.constant_adds _
  | inr a =>
    cases a with
    | inl s => exact Emit.constant_adds _
    | inr a =>
      rcases a with ⟨k, i, a⟩
      by_cases hk : k = tm.k₀
      · subst k
        simpa [bit, bitCost] using inputBit_adds tm C e word W i a
      · simpa [bit, bitCost, hk] using
          (Emit.constant_adds (I := Fin W) (oneHot (none : Option (tm.Γ k)) a))

theorem bitCost_le (a : Address tm C) : bitCost tm C word W a ≤ 6 := by
  have hb (i : Fin (C + 1)) : inputBitCost C word W i ≤ 6 := by
    unfold inputBitCost
    cases h : (tokens word W)[i.val]? with
    | none => simp
    | some token => cases token <;> simp
  cases a with
  | inl l => simp [bitCost]
  | inr a =>
    cases a with
    | inl s => simp [bitCost]
    | inr a =>
      rcases a with ⟨k, i, a⟩
      simp only [bitCost]
      split_ifs
      · exact hb i
      · omega

def cost : ℕ := ((addresses tm C).map (bitCost tm C word W)).sum

theorem adds : Emit.Adds (emit tm C e word W) (cost tm C word W) :=
  Emit.tabulate_adds _ _ _ _ (bit_adds tm C e word W)

theorem cost_le : cost tm C word W ≤ 6 * GateCost.width tm C := by
  have hb : ∀ xs : List (Address tm C), (xs.map (bitCost tm C word W)).sum ≤ 6 * xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
      have ha := bitCost_le tm C word W a
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  exact hb _

end Initial

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)
local instance sizeAlphabets : ∀ k, Fintype (w.verifier.tm.Γ k) := w.verifier.finiteAlphabets

theorem compileWord_gates (word : List Bool) :
    (compileWord w word).circuit.gates =
      Initial.cost w.verifier.tm (capacity w word) word (w.witnessLength.eval word.length) +
      (VerifierRun.horizonPolynomial w).eval word.length * GateCost.hold w.verifier.tm (capacity w word) := by
  change (Emit.finish (body w word) (fun i => i)).gates = _
  apply Emit.finish_gates
  simpa [body] using Emit.seq_adds
    (Initial.adds w.verifier.tm (capacity w word) w.verifier.inputAlphabet word _)
    (Emit.seq_adds (GateCost.unroll_adds w.verifier.tm (capacity w word) _)
      (Emit.route_adds (fun _ : Unit => acceptance w word)))

def gatePolynomial : Polynomial ℕ :=
  (Polynomial.C (6 * GateCost.width w.verifier.tm 0) +
    VerifierRun.horizonPolynomial w * Polynomial.C (GateCost.hold w.verifier.tm 0)) *
    (VerifierRun.capacityPolynomial w + Polynomial.C (VerifierRun.pushBudget w.verifier.tm + 1))

theorem compileWord_gates_le (word : List Bool) :
    (compileWord w word).circuit.gates ≤ (gatePolynomial w).eval word.length := by
  rw [compileWord_gates]
  have hi := Initial.cost_le w.verifier.tm (capacity w word) word (w.witnessLength.eval word.length)
  have hw := GateCost.width_le w.verifier.tm (capacity w word)
  have hs := GateCost.hold_le w.verifier.tm (capacity w word)
  have ht := Nat.mul_le_mul_left ((VerifierRun.horizonPolynomial w).eval word.length) hs
  simp only [gatePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have hc : (VerifierRun.capacityPolynomial w).eval word.length +
      (VerifierRun.pushBudget w.verifier.tm + 1) = capacity w word + 1 := by
    simp only [capacity, Nat.add_assoc]
  rw [hc]
  nlinarith

theorem compile_gates_le (a : α) :
    (compile w a).circuit.gates ≤ (gatePolynomial w).eval (ea.encode a).length :=
  compileWord_gates_le w _

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit
