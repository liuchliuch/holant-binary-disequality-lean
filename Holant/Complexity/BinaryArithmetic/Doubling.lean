import Holant.Complexity.BinaryArithmetic.Bits
import Holant.Complexity.StepCost

/-! A one-transition canonical binary doubling machine. The least-significant
zero bit is pushed only when the word is nonempty, so zero stays canonical.
This is a concrete finite-stack building block for future shift/add multiplication;
it does not claim a multiplication compiler. -/

namespace Holant.Complexity.BinaryArithmetic.Doubling

open Turing Computability
open Turing.TM2.Stmt

/-- Shift one place without replacing the empty canonical encoding of zero. -/
def shift : List Bool → List Bool
  | [] => []
  | bit :: rest => false :: bit :: rest

@[simp] theorem value_shift (word : List Bool) : value (shift word) = 2 * value word := by
  cases word <;> simp [shift, value]

theorem canonical_shift (word : List Bool) (h : Canonical word) : Canonical (shift word) := by
  cases word with
  | nil => trivial
  | cons bit rest => exact ⟨h, by simp⟩

theorem shift_encodeNat (n : ℕ) : shift (encodeNat n) = encodeNat (2 * n) := by
  apply canonical_injective
  · exact canonical_shift _ (canonical_encodeNat n)
  · exact canonical_encodeNat _
  · simp

/-- One binary stack, one control label, and three finite register states. -/
abbrev computer : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ := peek () (fun _ bit => bit)
    (branch Option.isSome
      (push () (fun _ => false) (load (fun _ => none) halt))
      (load (fun _ => none) halt))

@[simp] theorem step_shift (word : List Bool) :
    computer.step (initList computer word) = some (haltList computer (shift word)) := by
  cases word <;> simp [FinTM2.step, TM2.step, computer, initList, haltList, TM2.stepAux, shift] <;>
    congr 2

def outputs (word : List Bool) : TM2OutputsInTime computer word (some (shift word)) 1 where
  steps := 1
  evals_in_steps := step_shift word
  steps_le_m := Nat.le_refl 1

/-- A true constant-transition stack operation, with canonical binary input/output. -/
noncomputable def doublingPolyTime : PolyTime encodingNatBool encodingNatBool (fun n => 2 * n) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 1
  outputsFun n := by
    change TM2OutputsInTime computer (List.map id (encodeNat n))
      (some (List.map id (encodeNat (2 * n)))) ((1 : Polynomial ℕ).eval (encodeNat n).length)
    simpa only [List.map_id, Polynomial.eval_one, shift_encodeNat] using outputs (encodeNat n)
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

theorem doubling_inFP : InFP encodingNatBool encodingNatBool (fun n => 2 * n) :=
  ⟨doublingPolyTime⟩

theorem program_budget : TM2Cost.budget (computer.m ()) = 5 := rfl

end Holant.Complexity.BinaryArithmetic.Doubling
