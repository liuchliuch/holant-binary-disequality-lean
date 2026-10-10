import Holant.Proofs.Tractability.AffineMachine.Constraint


namespace Holant.LocalDrafts.Tractability.AffineMachine.FreePhase

open Holant.Tractable AffinePhase TwoTranslate
open scoped BigOperators

def tail {n : ℕ} (Q : QuadraticPhase (n + 1)) : QuadraticPhase n where
  constant := Q.constant
  linear j := Q.linear j.succ
  mixed j k := Q.mixed j.succ k.succ
  even_mixed j k h := Q.even_mixed j.succ k.succ (by simpa using h)

def neighbors {n : ℕ} (Q : QuadraticPhase (n + 1)) : Fin n → ZMod 2 :=
  fun j => if Q.mixed 0 j.succ = 0 then 0 else 1

theorem neighbors_lift {n : ℕ} (Q : QuadraticPhase (n + 1)) (j : Fin n) :
    evenLift (neighbors Q j) = Q.mixed 0 j.succ := by
  have h20 : (2 : ZMod 4) ≠ 0 := by decide
  rcases Q.even_mixed 0 j.succ (by simp) with h | h
  · simp only [neighbors, h, ite_true, evenLift_zero]
  · simp only [neighbors, h, h20, ite_false, evenLift_one]

theorem neighbor_sum {n : ℕ} (Q : QuadraticPhase (n + 1)) (x : Word n) :
    (∑ j, Q.mixed 0 j.succ * bitValue (ZMod 4) (x j)) = evenLift (dot (neighbors Q) x) := by
  rw [dot, evenLift_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases hx : x j <;> simp [bitValue, ← neighbors_lift Q j]

theorem eval_cons {n : ℕ} (Q : QuadraticPhase (n + 1)) (b : Bool) (x : Word n) :
    Q.eval (Fin.cons b x) = (tail Q).eval x + Q.linear 0 * bitValue (ZMod 4) b +
      bitValue (ZMod 4) b * evenLift (dot (neighbors Q) x) := by
  have hs : (∑ j, Q.mixed 0 j.succ * bitValue (ZMod 4) b * bitValue (ZMod 4) (x j)) =
      bitValue (ZMod 4) b * evenLift (dot (neighbors Q) x) := by
    rw [← neighbor_sum Q x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpos (j : Fin n) : (0 : Fin (n + 1)) < j.succ := by
    change 0 < j.val + 1
    exact Nat.zero_lt_succ j.val
  simp only [QuadraticPhase.eval, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.not_lt_zero, hpos, Fin.succ_lt_succ_iff, ite_false, ite_true,
    zero_add, Finset.sum_const_zero, tail]
  rw [hs]
  ring

/-- The phase multiplier is a fixed four-entry table. -/
noncomputable def multiplier (l : ZMod 4) : AlgebraicComplex :=
  if l = 0 then 2 else if l = 1 then 1 + imaginaryUnit else
    if l = 2 then 2 else 1 - imaginaryUnit

noncomputable def nextSupport {n : ℕ} (Q : QuadraticPhase (n + 1)) : AffineSystem n :=
  if Q.linear 0 = 0 then oneEquation (neighbors Q) 0 else
    if Q.linear 0 = 1 then AffineSystem.unconstrained n else
      if Q.linear 0 = 2 then oneEquation (neighbors Q) 1 else AffineSystem.unconstrained n

noncomputable def nextPhase {n : ℕ} (Q : QuadraticPhase (n + 1)) : QuadraticPhase n :=
  if Q.linear 0 = 0 then tail Q else
    if Q.linear 0 = 1 then Reconstruction.addParity (tail Q) (neighbors Q) (-1) else
      if Q.linear 0 = 2 then tail Q else Reconstruction.addParity (tail Q) (neighbors Q) 1

noncomputable def eliminate {n : ℕ} (A : State (n + 1)) : State n where
  scale := A.scale * multiplier (A.phase.linear 0)
  support := nextSupport A.phase
  phase := nextPhase A.phase

theorem rows_le_one {n : ℕ} (Q : QuadraticPhase (n + 1)) : (nextSupport Q).rows ≤ 1 := by
  by_cases h0 : Q.linear 0 = 0
  · simp only [nextSupport, h0, ite_true, oneEquation, le_refl]
  · by_cases h1 : Q.linear 0 = 1
    · simp only [nextSupport, if_neg h0, if_pos h1, AffineSystem.unconstrained]
      exact Nat.zero_le 1
    · by_cases h2 : Q.linear 0 = 2
      · simp only [nextSupport, if_neg h0, if_neg h1, if_pos h2, oneEquation]
        exact Nat.le_refl 1
      · simp only [nextSupport, if_neg h0, if_neg h1, if_neg h2, AffineSystem.unconstrained]
        exact Nat.zero_le 1

theorem value_eliminate {n : ℕ} (A : State (n + 1))
    (hp : Constraint.pivot A.support = none) (hb : Constraint.badRow A.support = false) (x : Word n) :
    A.value (Fin.cons false x) + A.value (Fin.cons true x) = (eliminate A).value x := by
  have hf := Constraint.no_pivot_holds A.support hp hb (Fin.cons false x)
  have ht := Constraint.no_pivot_holds A.support hp hb (Fin.cons true x)
  have hfalse : fourthRootPhase (A.phase.eval (Fin.cons false x)) =
      fourthRootPhase ((tail A.phase).eval x) := by
    calc
      fourthRootPhase (A.phase.eval (Fin.cons false x)) =
          fourthRootPhase ((tail A.phase).eval x + 0) := by
        simp only [eval_cons, bitValue_false, mul_zero, zero_mul, add_zero]
      _ = fourthRootPhase ((tail A.phase).eval x) * fourthRootPhase 0 :=
        fourthRootPhase_add _ _
      _ = fourthRootPhase ((tail A.phase).eval x) := by
        rw [fourthRootPhase_zero, mul_one]
  have htrue : fourthRootPhase (A.phase.eval (Fin.cons true x)) =
      fourthRootPhase ((tail A.phase).eval x) *
        fourthRootPhase (A.phase.linear 0 + evenLift (dot (neighbors A.phase) x)) := by
    rw [eval_cons]
    simp only [bitValue_true, mul_one, one_mul, add_assoc]
    exact fourthRootPhase_add _ _
  have hsum : A.value (Fin.cons false x) + A.value (Fin.cons true x) =
      A.scale * fourthRootPhase ((tail A.phase).eval x) *
        (1 + fourthRootPhase (A.phase.linear 0 + evenLift (dot (neighbors A.phase) x))) := by
    simp only [State.value, affineFormula, if_pos hf, if_pos ht, hfalse, htrue]
    ring
  rw [hsum]
  have h10 : (1 : ZMod 4) ≠ 0 := by decide
  have h20 : (2 : ZMod 4) ≠ 0 := by decide
  have h21 : (2 : ZMod 4) ≠ 1 := by decide
  have h30 : (3 : ZMod 4) ≠ 0 := by decide
  have h31 : (3 : ZMod 4) ≠ 1 := by decide
  have h32 : (3 : ZMod 4) ≠ 2 := by decide
  rcases fourth_cases (A.phase.linear 0) with h | h | h | h
  · simp only [State.value, affineFormula, eliminate, multiplier, nextSupport, nextPhase,
      h, ite_true, zero_add, phase_bracket_zero, oneEquation_holds]
    by_cases hx : dot (neighbors A.phase) x = 0 <;>
      simp [hx, mul_assoc, mul_comm, mul_left_comm]
  · simp only [State.value, affineFormula, eliminate, multiplier, nextSupport, nextPhase,
      h, h10, ite_false, ite_true, phase_bracket_one, AffineSystem.unconstrained_holds,
      Reconstruction.addParity_eval]
    rw [fourthRootPhase_add]
    ring
  · simp only [State.value, affineFormula, eliminate, multiplier, nextSupport, nextPhase,
      h, h20, h21, ite_false, ite_true, phase_bracket_two, oneEquation_holds]
    by_cases hx : dot (neighbors A.phase) x = 1 <;>
      simp [hx, mul_assoc, mul_comm, mul_left_comm]
  · simp only [State.value, affineFormula, eliminate, multiplier, nextSupport, nextPhase,
      h, h30, h31, h32, ite_false, phase_bracket_three, AffineSystem.unconstrained_holds,
      ite_true, Reconstruction.addParity_eval, one_mul]
    rw [fourthRootPhase_add]
    ring

theorem partition_eliminate {n : ℕ} (A : State (n + 1))
    (hp : Constraint.pivot A.support = none) (hb : Constraint.badRow A.support = false) :
    A.partition = (eliminate A).partition := by
  rw [State.partition, sum_split, State.partition]
  exact Finset.sum_congr rfl (fun x _ => value_eliminate A hp hb x)

/-- A nonzero generated neighbor is found by the same concrete scan next round. -/
theorem parity_pivot {n : ℕ} (a : Fin n → ZMod 2) (b : ZMod 2)
    (j : Fin n) (hj : a j ≠ 0) :
    ∃ p, Constraint.pivot (oneEquation a b) = some p := by
  cases h : Constraint.pivot (oneEquation a b) with
  | none =>
      let r : Fin (oneEquation a b).rows := ⟨0, by change 0 < 1; decide⟩
      have hz : a j = 0 := by
        simpa only [oneEquation] using Constraint.pivot_none (oneEquation a b) h r j
      exact False.elim (hj hz)
  | some p => exact ⟨p, rfl⟩

theorem trivial_parity_bad {n : ℕ} (a : Fin n → ZMod 2) (ha : ∀ j, a j = 0) :
    Constraint.badRow (oneEquation a 1) = true := by
  let r : Fin (oneEquation a 1).rows := ⟨0, by change 0 < 1; decide⟩
  apply (Constraint.badRow_spec _).mpr
  refine ⟨r, ?_, ?_⟩
  · intro j
    change a j = 0
    exact ha j
  · change (1 : ZMod 2) ≠ 0
    decide

end Holant.LocalDrafts.Tractability.AffineMachine.FreePhase
