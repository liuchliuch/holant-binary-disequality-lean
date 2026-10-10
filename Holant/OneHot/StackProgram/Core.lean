import Holant.OneHot.ArithmeticSizeTree
import Mathlib.Data.Fintype.Option

/-!
# Finite stack instruction syntax for one-hot evaluation

Unlike `Arithmetic`, code has no field-valued continuation. Instructions contain
only a coefficient label and a bounded stack index. An interpretation is supplied
only to the interpreter. Arithmetic traces record the actual ordered operands and
result of every executed addition and multiplication. Underflow returns `none`.
-/

namespace Holant.OneHot.StackProgram

variable {A K : Type*}

/-- The complete instruction alphabet. `copy` and `erase` access only the first
eight stack cells; this fixed window suffices for the tree compiler. -/
inductive Op (A : Type*) where
  | literal (label : A)
  | zero
  | one
  | copy (index : Fin 8)
  | erase (index : Fin 8)
  | swap
  | add
  | mul
  deriving DecidableEq, Repr

abbrev Code (A : Type*) := List (Op A)

/-- Removing a missing cell is an error, rather than a silent no-op. -/
def eraseAt : ℕ → List K → Option (List K)
  | _, [] => none
  | 0, _ :: xs => some xs
  | n + 1, x :: xs => (eraseAt n xs).map (x :: ·)

variable [CommSemiring K]

/-- One instruction, with the arithmetic event it actually executes. -/
def step (coeff : A → K) : Op A → List K → Option (List K × List K)
  | .literal a, s => some (coeff a :: s, [])
  | .zero, s => some (0 :: s, [])
  | .one, s => some (1 :: s, [])
  | .copy i, s => (s[i.val]?).map (fun x => (x :: s, []))
  | .erase i, s => (eraseAt i.val s).map (fun s' => (s', []))
  | .swap, x :: y :: s => some (y :: x :: s, [])
  | .add, x :: y :: s => some ((x + y) :: s, [x, y, x + y])
  | .mul, x :: y :: s => some ((x * y) :: s, [x, y, x * y])
  | _, _ => none

/-- Explicit finite interpreter. Failure aborts, without fabricating a value. -/
def run (coeff : A → K) : Code A → List K → Option (List K × List K)
  | [], s => some (s, [])
  | op :: code, s => do
    let (s', event) ← step coeff op s
    let (s'', events) ← run coeff code s'
    pure (s'', event ++ events)

/-- Sequential execution composes both final stacks and actual traces. -/
theorem run_append (coeff : A → K) (p q : Code A) (s : List K) :
    run coeff (p ++ q) s = (do
      let (s', t) ← run coeff p s
      let (s'', u) ← run coeff q s'
      pure (s'', t ++ u)) := by
  induction p generalizing s with
  | nil => simp [run]
  | cons op p ih =>
    simp only [List.cons_append, run, ih]
    cases h : step coeff op s with
    | none => simp
    | some v =>
      rcases v with ⟨s', t⟩
      cases h' : run coeff p s' with
      | none => simp [h']
      | some v =>
        rcases v with ⟨s'', u⟩
        cases h'' : run coeff q s'' <;> simp [h', h'', List.append_assoc]

@[simp] theorem run_nil (coeff : A → K) (s : List K) :
    run coeff [] s = some (s, []) := rfl

/-- A checked composition rule avoids reasoning about unexecuted paths. -/
theorem run_append_of (coeff : A → K) {p q : Code A} {s s' s'' t u : List K}
    (hp : run coeff p s = some (s', t))
    (hq : run coeff q s' = some (s'', u)) :
    run coeff (p ++ q) s = some (s'', t ++ u) := by
  simp [run_append, hp, hq]

/-- `Safe` quantifies over precisely the executed arithmetic operands/results. -/
def Safe (coeff : A → K) (P : K → Prop) (code : Code A) (s : List K) : Prop :=
  ∃ s' trace, run coeff code s = some (s', trace) ∧ ∀ x ∈ trace, P x

end Holant.OneHot.StackProgram
