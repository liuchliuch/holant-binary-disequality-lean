import Holant.Proofs.Tractability.AffineMachine.RawMachine
import Holant.Proofs.Tractability.AffineMachine.ConstraintRefinement
import Holant.Proofs.Tractability.AffineMachine.FreeRefinement


namespace Holant.LocalDrafts.Tractability.AffineMachine.WireCorrectness

open Holant.Tractable AffinePhase TwoTranslate EncodedTable ProductMachine
open ReadRefinement

variable {s b : ℕ}

def output (x : WireRound.State (s := s) (b := b)) := WireRound.finish (WireLoop.value x)

theorem finish_size (x : WireRound.State (s := s) (b := b)) :
    (WireRound.finish x).size ≤ x.2.size + 2 := by
  unfold WireRound.finish
  split <;> simp [Expr.size]

theorem output_size (x : WireRound.State (s := s) (b := b)) :
    (output x).size ≤ x.2.size + 2 * x.1.1 + 2 :=
  (finish_size (WireLoop.value x)).trans
    (Nat.add_le_add_right (WireSize.expression_iterate x x.1.1) 2)

theorem iterate_stopped (x : WireRound.State (s := s) (b := b)) (h : x.1.1 = 0) (k : ℕ) :
    (WireRound.step^[k]) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, WireRound.stable x h]

theorem active_run {n : ℕ} (x y : WireRound.State (s := s) (b := b))
    (hx : x.1.1 = n + 1) (hy : y.1.1 = n) (hstep : WireRound.step x = y) :
    WireLoop.value x = WireLoop.value y := by
  simp only [WireLoop.value, hx, hy, Function.iterate_succ_apply, hstep]

/-- The pivot coordinates below are obtained from the actual bounded candidate
list. They are not requested from the caller of the evaluator. -/
theorem selected_pivot {n : ℕ} (T : Dense.Table n)
    (hp : (PivotPrograms.selected (store T)).1 = true) :
    ∃ r : Fin T.rows, ∃ j : Fin n,
      (PivotPrograms.selected (store T)).2 = (r.val, j.val) ∧ T.support.matrix r j = 1 := by
  obtain ⟨hr, hj, hc⟩ := PivotPrograms.selected_valid (store T) hp
  let r : Fin T.rows := ⟨(PivotPrograms.selected (store T)).2.1, by simpa [store, Dense.Table.support] using hr⟩
  let j : Fin n := ⟨(PivotPrograms.selected (store T)).2.2, hj⟩
  refine ⟨r, j, rfl, ?_⟩
  have he := coefficient_store T r j
  have hdec : decide (T.support.matrix r j = 1) = true := he.symm.trans hc
  exact of_decide_eq_true hdec

theorem partition_correct (c : (Fin s ⊕ Fin b) → AlgebraicComplex) :
    ∀ {n : ℕ} (T : Dense.Table n) (e : Expr (RawCode.Label (s := s) (b := b))),
      (output (store T, e)).eval (ScalarCode.coefficient c) =
        (T.state (e.eval (ScalarCode.coefficient c))).partition := by
  intro n
  induction n with
  | zero =>
    intro T e
    cases hb : Constraint.badRow T.support with
    | false =>
      rw [nullary_partition (T.state _) hb]
      simp [output, WireLoop.value, WireRound.finish, show (store T).1 = 0 from rfl,
        badRows_store, hb, Expr.eval, ScalarCode.coefficient, constant,
        Dense.Table.state, Dense.Table.phase]
      exact Or.inl rfl
    | true =>
      rw [Constraint.partition_badRow (T.state _) hb]
      simp [output, WireLoop.value, WireRound.finish, badRows_store,
        hb, Expr.eval, show (store T).1 = 0 from rfl]
  | succ n ih =>
    intro T e
    cases hb : PivotPrograms.badRows (store T) with
    | true =>
      have hb' : Constraint.badRow T.support = true := by rwa [badRows_store] at hb
      rw [Constraint.partition_badRow (T.state _) hb']
      have he : WireRound.step (store T, e) = WireRound.dead (store T, e) := by
        simp [WireRound.step, hb, show (store T).1 = n + 1 from rfl]
      have hr : WireLoop.value (store T, e) = WireRound.dead (store T, e) := by
        change (WireRound.step^[n + 1]) (store T, e) = _
        rw [Function.iterate_succ_apply, he, iterate_stopped _ rfl]
      simp [output, hr, WireRound.finish, WireRound.dead, PivotPrograms.badRows,
        Expr.eval, constant]
    | false =>
      cases hp : (PivotPrograms.selected (store T)).1 with
      | true =>
        obtain ⟨r, j, hpj, hj⟩ := selected_pivot T hp
        let U := FiniteCore.pivotStep T r j
        have he : WireRound.step (store T, e) = (store U, e) := by
          simp only [WireRound.step, show (store T).1 = n + 1 from rfl,
            Nat.succ_ne_zero, if_false, hb, hp, Bool.false_eq_true, if_true, hpj]
          exact congrArg (fun d => (d, e)) (ConstraintRefinement.value_store T r j hj)
        have hr := active_run (store T, e) (store U, e) rfl rfl he
        change (WireRound.finish (WireLoop.value (store T, e))).eval _ = _
        rw [hr, show WireRound.finish (WireLoop.value (store U, e)) = output (store U, e) from rfl, ih]
        rw [show U = Dense.pivotStep T r j from FiniteCore.pivotStep_eq T r j, Dense.pivotStep_state]
        exact (Constraint.partition_eliminate (T.state _) r j hj).symm
      | false =>
        let U := FreeRefinement.normalized T
        let f : Expr (RawCode.Label (s := s) (b := b)) :=
          .mul e (.literal (.inr (.inr (T.phase.linear 0))))
        have hl : FreeRewrite.headLinear (store T) = T.phase.linear 0 := store_linear T 0
        have he : WireRound.step (store T, e) = (store U, f) := by
          simp only [WireRound.step, show (store T).1 = n + 1 from rfl,
            Nat.succ_ne_zero, if_false, hb, hp, Bool.false_eq_true,
            FreeRefinement.value_store, hl]
          rfl
        have hr := active_run (store T, e) (store U, f) rfl rfl he
        change (WireRound.finish (WireLoop.value (store T, e))).eval _ = _
        rw [hr, show WireRound.finish (WireLoop.value (store U, f)) = output (store U, f) from rfl, ih]
        simpa only [f, Expr.eval, ScalarCode.coefficient] using
          FreeRefinement.partition_store T (e.eval (ScalarCode.coefficient c)) hp hb

/-- The connection to FiniteCore is value equality; unused phase coefficients
and hence syntactic expression trees need not be definitionally identical. -/
theorem finiteCore_value (c : (Fin s ⊕ Fin b) → AlgebraicComplex) {n : ℕ}
    (T : Dense.Table n) (e : Expr (RawCode.Label (s := s) (b := b))) :
    (output (store T, e)).eval (ScalarCode.coefficient c) =
      (FiniteCore.compile T e).eval (ScalarCode.coefficient c) := by
  rw [partition_correct, FiniteCore.compile_correct]

end Holant.LocalDrafts.Tractability.AffineMachine.WireCorrectness
