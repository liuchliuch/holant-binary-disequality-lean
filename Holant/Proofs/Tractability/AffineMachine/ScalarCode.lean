import Holant.Proofs.Tractability.AffineMachine.Dense
import Holant.Proofs.Tractability.ProductMachine.FieldInterpreter


namespace Holant.LocalDrafts.Tractability.AffineMachine.ScalarCode

open Holant.Tractable AffinePhase TwoTranslate
open ProductMachine

abbrev Atom (A : Type) := A ⊕ (ZMod 4 ⊕ ZMod 4)

noncomputable def coefficient {A : Type} (c : A → AlgebraicComplex) : Atom A → AlgebraicComplex
  | .inl a => c a
  | .inr (.inl q) => fourthRootPhase q
  | .inr (.inr q) => FreePhase.multiplier q

/-- The initial accumulator contains the actual product of local scales. -/
noncomputable def compile {A : Type} : {n : ℕ} → Dense.Table n → Expr (Atom A) → Expr (Atom A)
  | 0, T, e => if Constraint.badRow T.support then .zero else .mul e (.literal (.inr (.inl T.constant)))
  | n + 1, T, e => if Constraint.badRow T.support then .zero else
      match Constraint.pivot T.support with
      | some (r, j) => compile (Dense.pivotStep T r j) e
      | none => compile (Dense.freeStep T) (.mul e (.literal (.inr (.inr (T.phase.linear 0)))))

theorem compile_correct {A : Type} (c : A → AlgebraicComplex) :
    ∀ {n : ℕ} (T : Dense.Table n) (e : Expr (Atom A)),
    (compile T e).eval (coefficient c) = (T.state (e.eval (coefficient c))).partition := by
  intro n
  induction n with
  | zero =>
    intro T e
    cases hb : Constraint.badRow T.support with
    | true => simpa [compile, hb, Expr.eval] using (Constraint.partition_badRow (T.state _) hb).symm
    | false => simpa [compile, hb, Expr.eval, coefficient, Dense.Table.state, Dense.Table.phase] using
        (nullary_partition (T.state (e.eval (coefficient c))) hb).symm
  | succ n ih =>
    intro T e
    cases hb : Constraint.badRow T.support with
    | true => simpa [compile, hb, Expr.eval] using (Constraint.partition_badRow (T.state _) hb).symm
    | false =>
      cases hp : Constraint.pivot T.support with
      | some p =>
        rcases p with ⟨r, j⟩
        rw [compile, if_neg (by simp [hb]), hp, ih]
        have hs := Dense.pivotStep_state T (e.eval (coefficient c)) r j
        exact (congrArg State.partition hs).trans (Constraint.partition_eliminate (T.state _) r j (Constraint.pivot_some _ r j hp)).symm
      | none =>
        rw [compile, if_neg (by simp [hb]), hp, ih]
        simp only [Expr.eval, coefficient, Dense.freeStep_state]
        exact (FreePhase.partition_eliminate (T.state _) hp hb).symm

theorem compile_size {A : Type} : ∀ {n : ℕ} (T : Dense.Table n) (e : Expr (Atom A)),
    (compile T e).size ≤ e.size + 2 * n + 2 := by
  intro n
  induction n with
  | zero => intro T e; unfold compile; split <;> simp [Expr.size]
  | succ n ih =>
    intro T e
    unfold compile
    split
    · simp [Expr.size]
    · split
      · exact (ih _ _).trans (by omega)
      · have h := ih (Dense.freeStep T) (.mul e (.literal (.inr (.inr (T.phase.linear 0)))))
        simp only [Expr.size] at h
        omega

theorem bytecode_length {A : Type} {n : ℕ} (T : Dense.Table n) (e : Expr (Atom A)) :
    (compile T e).code.length ≤ e.size + 2 * n + 2 := by
  rw [Expr.code_length]
  exact compile_size T e

open Computability Holant.Complexity Holant.Algebraic

/-- Applies to the actual existing fixed-field interpreter, on already emitted
code. Connecting raw graph bytes to this code remains a separate obligation. -/
theorem coordinate_bound {A K : Type} [Fintype A] [DecidableEq A]
    [Field K] [Algebra ℚ K] {d n : ℕ} (F : FixedField K d)
    (table : Atom A → Fin d → ℚ) (T : Dense.Table n) (e : Expr (Atom A)) :
    (∀ i, rationalBitHeight (F.decode.symm ((compile T e).eval
      (FieldInterpreter.coefficients F table)) i) ≤ FieldInterpreter.width F table (e.size + 2 * n + 2)) ∧
    ∀ x ∈ (compile T e).trace (FieldInterpreter.coefficients F table), ∀ i,
      rationalBitHeight (F.decode.symm x i) ≤ FieldInterpreter.width F table (e.size + 2 * n + 2) :=
  FieldInterpreter.coordinate_trace_bound F table _ _ (compile_size T e)

end Holant.LocalDrafts.Tractability.AffineMachine.ScalarCode
