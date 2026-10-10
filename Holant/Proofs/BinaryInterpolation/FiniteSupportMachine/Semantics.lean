import Holant.Proofs.BinaryInterpolation.FiniteSupportMachine.Elimination


namespace Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Semantics

open Holant.Tractable AffinePhase TwoTranslate
open Holant.LocalDrafts.Tractability.AffineMachine
open EncodedTable (Row)
open Holant.LocalDrafts.MainChain

def run : ℕ → List Row → Option (List Bool)
  | 0, rs => if Elimination.bad (0, rs) then none else some []
  | n + 1, rs =>
    let d : Codec.Matrix := (n + 1, rs)
    if Elimination.bad d then none else
      let p := Elimination.selected d
      if p.1 then
        (run n (Elimination.update (d, p.2)).2).map
          (fun w => BackSubstitution.value (Elimination.save (d, p.2), w))
      else some (List.replicate (n + 1) false)

def solve (d : Codec.Matrix) : Option (List Bool) := run d.1 (Codec.normalize d).2
def Satisfies (d : Codec.Matrix) (w : List Bool) : Prop :=
  w.length = d.1 ∧ (Codec.support d).Holds (fun j => w.getD j.val false)

theorem run_bad {n : ℕ} (S : AffineSystem n)
    (hb : Constraint.badRow S = true) : run n (Codec.pack S).2 = none := by
  have hb' : Elimination.bad (Codec.pack S) = true := (Elimination.bad_pack S).trans hb
  cases n with
  | zero =>
    change (if Elimination.bad (Codec.pack S) then none else some []) = none
    simp [hb']
  | succ n =>
    change (if Elimination.bad (Codec.pack S) then none else _) = none
    simp [hb']

theorem run_pivot {n : ℕ} (S : AffineSystem (n + 1))
    (hb : Constraint.badRow S = false) (hp : (Elimination.selected (Codec.pack S)).1 = true)
    (r : Fin S.rows) (j : Fin (n + 1))
    (he : (Elimination.selected (Codec.pack S)).2 = (r.val, j.val))
    (hj : S.matrix r j = 1) :
    run (n + 1) (Codec.pack S).2 =
      (run n (Codec.pack (LocalAffineSupportSolver.descend S r j)).2).map
        (fun w => BackSubstitution.value (BackSubstitution.save S r j, w)) := by
  change (if Elimination.bad (Codec.pack S) then none else
    if (Elimination.selected (Codec.pack S)).1 then
      (run n (Elimination.update (Codec.pack S, (Elimination.selected (Codec.pack S)).2)).2).map
        (fun w => BackSubstitution.value
          (Elimination.save (Codec.pack S, (Elimination.selected (Codec.pack S)).2), w))
    else some (List.replicate (n + 1) false)) = _
  simp only [Elimination.bad_pack, hb, hp, Bool.false_eq_true, Bool.coe_true, if_false, if_true, he]
  rw [Elimination.update_pack S r j hj, Elimination.save_pack]

theorem run_free {n : ℕ} (S : AffineSystem (n + 1))
    (hb : Constraint.badRow S = false) (hp : (Elimination.selected (Codec.pack S)).1 = false) :
    run (n + 1) (Codec.pack S).2 = some (List.replicate (n + 1) false) := by
  change (if Elimination.bad (Codec.pack S) then none else
    if (Elimination.selected (Codec.pack S)).1 then _ else _) = _
  simp only [Elimination.bad_pack, hb, hp, Bool.false_eq_true, if_false]

theorem sound : ∀ (n : ℕ) (S : AffineSystem n) (w : List Bool),
    run n (Codec.pack S).2 = some w → ∃ x : Word n, w = List.ofFn x ∧ S.Holds x := by
  intro n
  induction n with
  | zero =>
    intro S w hw
    cases hb : Constraint.badRow S with
    | true => rw [run_bad S hb] at hw; cases hw
    | false =>
      have hr : run 0 (Codec.pack S).2 = some [] := by
        change (if Elimination.bad (Codec.pack S) then none else some []) = _
        simp [Elimination.bad_pack, hb]
      have he : w = [] := by simpa [hr] using hw.symm
      exact ⟨Fin.elim0, by simpa using he, LocalAffineSupportSolver.nullary_holds S hb⟩
  | succ n ih =>
    intro S w hw
    cases hb : Constraint.badRow S with
    | true => rw [run_bad S hb] at hw; cases hw
    | false =>
      cases hp : (Elimination.selected (Codec.pack S)).1 with
      | false =>
        rw [run_free S hb hp] at hw
        refine ⟨FiniteCore.zeroWord (n + 1), ?_,
          Constraint.no_pivot_holds S (Elimination.no_pivot_pack S hp) hb _⟩
        simpa [FiniteCore.zeroWord, List.replicate_succ] using hw.symm
      | true =>
        obtain ⟨r, j, he, hj⟩ := Elimination.selected_pack_valid S hp
        rw [run_pivot S hb hp r j he hj] at hw
        cases hy : run n (Codec.pack (LocalAffineSupportSolver.descend S r j)).2 with
        | none => simp [hy] at hw
        | some v =>
          obtain ⟨x, hx, hs⟩ := ih (LocalAffineSupportSolver.descend S r j) v hy
          refine ⟨FiniteCore.solve S r j x, ?_, ?_⟩
          · simpa [hy, hx, BackSubstitution.value_exact S r j hj] using hw.symm
          · rw [LocalAffineSupportSolver.descend_eq, AffineSystem.pullback_holds _ _
              (Constraint.solveMap_affine S r j)] at hs
            simpa only [FiniteCore.solve_eq] using hs

theorem complete : ∀ (n : ℕ) (S : AffineSystem n),
    (∃ x, S.Holds x) → ∃ w, run n (Codec.pack S).2 = some w := by
  intro n
  induction n with
  | zero =>
    intro S hs
    obtain ⟨x, hx⟩ := hs
    cases hb : Constraint.badRow S with
    | true => exact (Constraint.badRow_no_solution S hb x hx).elim
    | false =>
      refine ⟨[], ?_⟩
      change (if Elimination.bad (Codec.pack S) then none else some []) = _
      simp [Elimination.bad_pack, hb]
  | succ n ih =>
    intro S hs
    obtain ⟨x, hx⟩ := hs
    cases hb : Constraint.badRow S with
    | true => exact (Constraint.badRow_no_solution S hb x hx).elim
    | false =>
      cases hp : (Elimination.selected (Codec.pack S)).1 with
      | false => exact ⟨_, run_free S hb hp⟩
      | true =>
        obtain ⟨r, j, he, hj⟩ := Elimination.selected_pack_valid S hp
        obtain ⟨v, hv⟩ := ih (LocalAffineSupportSolver.descend S r j)
          (LocalAffineSupportSolver.descend_has_solution S r j hj x hx)
        exact ⟨_, by rw [run_pivot S hb hp r j he hj, hv]; rfl⟩

theorem run_none_iff (n : ℕ) (S : AffineSystem n) :
    run n (Codec.pack S).2 = none ↔ ¬ ∃ x, S.Holds x := by
  constructor
  · intro hn hs
    obtain ⟨w, hw⟩ := complete n S hs
    simp [hn] at hw
  · intro hn
    cases hw : run n (Codec.pack S).2 with
    | none => rfl
    | some w =>
      obtain ⟨x, _, hx⟩ := sound n S w hw
      exact (hn ⟨x, hx⟩).elim

theorem solve_sound (d : Codec.Matrix) (w : List Bool) (h : solve d = some w) : Satisfies d w := by
  have hr : run d.1 (Codec.pack (Codec.support d)).2 = some w := by
    simpa only [solve, Codec.pack_support] using h
  obtain ⟨x, rfl, hx⟩ := sound d.1 (Codec.support d) w hr
  exact ⟨by simp, by simpa only [DensePrograms.getD_ofFn] using hx⟩

theorem solve_none_iff (d : Codec.Matrix) : solve d = none ↔ ¬ ∃ x, (Codec.support d).Holds x := by
  simpa only [solve, Codec.pack_support] using run_none_iff d.1 (Codec.support d)

/-- The encoded solver and root specification have the same inconsistency
answer. They need not return the same witness to a nonunique system. -/
theorem none_iff_root (d : Codec.Matrix) :
    solve d = none ↔ LocalAffineSupportSolver.solve (Codec.support d) = none := by
  rw [solve_none_iff, LocalAffineSupportSolver.solve_none_iff]

end Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine.Semantics
