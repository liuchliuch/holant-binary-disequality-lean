import Holant.Proofs.BinaryInterpolation.FiniteSupportMachine.Controller


namespace Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.ControllerSemantics

open Holant.LocalDrafts.Tractability.AffineMachine
open Controller

def unwind : Frames → Option (List Bool) → Option (List Bool)
  | [], w => w
  | f :: fs, w => unwind fs (w.map (fun x => BackSubstitution.value (f, x)))

@[simp] theorem unwind_none (fs : Frames) : unwind fs none = none := by
  induction fs with
  | nil => rfl
  | cons f fs ih => exact ih

def meaning (s : State) : Option (List Bool) :=
  if s.1.2 then none else
    if s.1.1 then unwind s.2.2.1 (Semantics.run s.2.1.1 s.2.1.2)
    else unwind s.2.2.1 (some s.2.2.2)

theorem selected_zero (rs : List EncodedTable.Row) : (Elimination.selected (0, rs)).1 = false := by
  cases hp : (Elimination.selected (0, rs)).1 with
  | false => rfl
  | true =>
    have hj := (PivotPrograms.selected_valid (Codec.lift (0, rs)) hp).2.1
    simp [Codec.lift] at hj

theorem run_equation (d : Codec.Matrix) :
    Semantics.run d.1 d.2 =
      if Elimination.bad d then none else
        if (Elimination.selected d).1 then
          (Semantics.run (d.1 - 1) (Elimination.update (d, (Elimination.selected d).2)).2).map
            (fun w => BackSubstitution.value (Elimination.save (d, (Elimination.selected d).2), w))
        else some (List.replicate d.1 false) := by
  rcases d with ⟨n, rs⟩
  cases n with
  | zero => simp [Semantics.run, selected_zero]
  | succ n => rfl

@[simp] theorem meaning_initial (d : Codec.Matrix) : meaning (initial d) = Semantics.solve d := rfl

theorem meaning_step (s : State) : meaning (step s) = meaning s := by
  cases hf : s.1.2 with
  | true => simp [step, hf]
  | false =>
    cases hd : s.1.1 with
    | true =>
      cases hb : Elimination.bad s.2.1 with
      | true =>
        simp only [step, hf, hd, hb, Bool.false_eq_true, Bool.coe_true, if_false, if_true]
        simp only [meaning, failed, hf, hd, Bool.false_eq_true, Bool.coe_true, if_false, if_true]
        rw [run_equation]
        simp [hb]
      | false =>
        cases hp : (Elimination.selected s.2.1).1 with
        | false =>
          simp only [step, hf, hd, hb, hp, Bool.false_eq_true, Bool.coe_true, if_false, if_true]
          simp only [meaning, free, hf, hd, Bool.false_eq_true, Bool.coe_true, if_false, if_true]
          rw [run_equation]
          simp [hb, hp]
        | true =>
          simp only [step, hf, hd, hb, hp, Bool.false_eq_true, Bool.coe_true, if_false, if_true]
          simp only [meaning, pivot, hf, hd, Bool.false_eq_true, Bool.coe_true,
            if_false, if_true, unwind]
          rw [run_equation s.2.1]
          simp [hb, hp, pivotContext, Elimination.dimension_update]
    | false =>
      cases hs : s.2.2.1 with
      | nil => simp [step, hf, hd, hs]
      | cons f fs =>
        simp [step, hf, hd, hs, meaning, back, unwind]

theorem meaning_iterate (s : State) (k : ℕ) : meaning ((step^[k]) s) = meaning s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', meaning_step, ih]

theorem terminal_answer (s : State) (h : Terminal s) : answer s = meaning s := by
  rcases h with hf | ⟨hd, hs⟩
  · simp [answer, meaning, hf]
  · simp [answer, meaning, hd, hs, unwind]

theorem initial_measure (d : Codec.Matrix) : measure (initial d) = 2 * d.1 + 1 := rfl

/-- The `2n+1` budget includes the zero-dimensional consistency test and the
switch to reconstruction. No input certificate or progress premise is used. -/
theorem answer_iterate (d : Codec.Matrix) (k : ℕ) (hk : 2 * d.1 + 1 ≤ k) :
    answer ((step^[k]) (initial d)) = Semantics.solve d := by
  rw [terminal_answer _ (terminal_iterate _ k (by simpa [initial_measure] using hk)),
    meaning_iterate, meaning_initial]

theorem iterate_sound (d : Codec.Matrix) (k : ℕ) (hk : 2 * d.1 + 1 ≤ k)
    (w : List Bool) (hw : answer ((step^[k]) (initial d)) = some w) : Semantics.Satisfies d w := by
  rw [answer_iterate d k hk] at hw
  exact Semantics.solve_sound d w hw

theorem iterate_none_iff (d : Codec.Matrix) (k : ℕ) (hk : 2 * d.1 + 1 ≤ k) :
    answer ((step^[k]) (initial d)) = none ↔ ¬ ∃ x, (Codec.support d).Holds x := by
  rw [answer_iterate d k hk, Semantics.solve_none_iff]

end Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.ControllerSemantics
