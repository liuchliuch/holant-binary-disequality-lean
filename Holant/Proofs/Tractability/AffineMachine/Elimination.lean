import Holant.Proofs.Tractability.AffineMachine.FreePhase


namespace Holant.LocalDrafts.Tractability.AffineMachine

open Holant.Tractable AffinePhase TwoTranslate
open scoped BigOperators

noncomputable def evaluate : {n : ℕ} → State n → AlgebraicComplex
  | 0, A => if Constraint.badRow A.support then 0 else A.scale * fourthRootPhase A.phase.constant
  | n + 1, A =>
    if Constraint.badRow A.support then 0 else
      match Constraint.pivot A.support with
      | some (r, j) => evaluate (Constraint.eliminate A r j)
      | none => evaluate (FreePhase.eliminate A)

theorem nullary_partition (A : State 0) (hb : Constraint.badRow A.support = false) :
    A.partition = A.scale * fourthRootPhase A.phase.constant := by
  have hp : Constraint.pivot A.support = none := by
    have he : (List.finRange A.support.rows).flatMap (fun _ => ([] : List (Fin A.support.rows × Fin 0))) = [] :=
      List.flatMap_eq_nil_iff.mpr (by intros; rfl)
    simp [Constraint.pivot,Constraint.positions,Constraint.first,he]
  have hh := Constraint.no_pivot_holds A.support hp hb
  simp [State.partition, State.value, affineFormula, hh, QuadraticPhase.eval]

theorem evaluate_eq_partition : ∀ {n : ℕ} (A : State n), evaluate A = A.partition := by
  intro n
  induction n with
  | zero =>
    intro A
    cases hb : Constraint.badRow A.support with
    | false => simpa [evaluate, hb] using (nullary_partition A hb).symm
    | true => simpa [evaluate, hb] using (Constraint.partition_badRow A hb).symm
  | succ n ih =>
    intro A
    cases hb : Constraint.badRow A.support with
    | true => simpa [evaluate, hb] using (Constraint.partition_badRow A hb).symm
    | false =>
      cases hp : Constraint.pivot A.support with
      | none =>
        simpa [evaluate, hb, hp, ih] using (FreePhase.partition_eliminate A hp hb).symm
      | some p =>
        rcases p with ⟨r, j⟩
        simpa [evaluate, hb, hp, ih] using
          (Constraint.partition_eliminate A r j (Constraint.pivot_some _ r j hp)).symm

/-- Count actual recursive eliminations; inconsistency can stop early. -/
noncomputable def rounds : {n : ℕ} → State n → ℕ
  | 0, _ => 0
  | n + 1, A => if Constraint.badRow A.support then 0 else
      match Constraint.pivot A.support with
      | some (r, j) => 1 + rounds (Constraint.eliminate A r j)
      | none => 1 + rounds (FreePhase.eliminate A)

theorem rounds_le : ∀ {n : ℕ} (A : State n), rounds A ≤ n := by
  intro n
  induction n with
  | zero => intro A; simp [rounds]
  | succ n ih =>
    intro A
    unfold rounds
    split
    · omega
    · split <;> simpa only [Nat.add_comm] using Nat.add_le_add_left (ih _) 1

/-- Row counts cannot grow beyond the initial rows or the single parity row. -/
theorem constraint_rows {n : ℕ} (A : State (n + 1))
    (r : Fin A.support.rows) (j : Fin (n + 1)) :
    (Constraint.eliminate A r j).support.rows = A.support.rows := rfl

theorem free_rows {n : ℕ} (A : State (n + 1)) :
    (FreePhase.eliminate A).support.rows ≤ 1 := FreePhase.rows_le_one A.phase

end Holant.LocalDrafts.Tractability.AffineMachine
