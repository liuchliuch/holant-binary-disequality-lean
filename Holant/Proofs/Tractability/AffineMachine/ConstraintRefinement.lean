import Holant.Proofs.Tractability.AffineMachine.ReadRefinement
import Holant.Proofs.Tractability.AffineMachine.ConstraintRewrite


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.AffineMachine.ConstraintRefinement

open Holant.Tractable AffinePhase TwoTranslate EncodedTable
open ReadRefinement SampleRefinement
open scoped BigOperators

def context {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows) (j : Fin (n + 1)) :
    ConstraintRewrite.Context := (store T, r.val, j.val)

theorem before_bit {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows)
    (j k : Fin (n + 1)) (m : SamplePrograms.Mask) :
    ConstraintRewrite.beforeBit (context T r j, m) k.val =
      Fin.cons (α := fun _ => Bool) false (assignment n m) (Equiv.swap 0 j k) := by
  by_cases hkj : k = j
  · subst k
    simp [ConstraintRewrite.beforeBit, context]
  · by_cases hk : k = 0
    · subst k
      cases j using Fin.cases with
      | zero => exact False.elim (hkj rfl)
      | succ t => simp [ConstraintRewrite.beforeBit, context, assignment]
    · cases k using Fin.cases with
      | zero => exact False.elim (hk rfl)
      | succ t =>
        have hn : t.succ.val ≠ j.val := fun h => hkj (Fin.ext h)
        simp [ConstraintRewrite.beforeBit, context, hn, assignment,
          Equiv.swap_apply_of_ne_of_ne hk hkj]
        simpa only [Fin.val_succ] using fun _ => hn

theorem before_word {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows)
    (j : Fin (n + 1)) (m : SamplePrograms.Mask) :
    ConstraintRewrite.before (context T r j, m) =
      List.ofFn (permute j (Fin.cons false (assignment n m))) := by
  rw [ConstraintRewrite.before, DensePrograms.range_map]
  congr 1; funext k
  exact before_bit T r j k m

theorem bit2_xor (a b : Bool) : FiniteCore.bit2 (Bool.xor a b) = FiniteCore.bit2 a + FiniteCore.bit2 b := by
  cases a <;> cases b <;> decide

theorem sub_two (a b : ZMod 2) : a - b = a + b := by fin_cases a <;> fin_cases b <;> decide

theorem bit2_injective : Function.Injective FiniteCore.bit2 := by
  intro a b h
  cases a <;> cases b <;> simp_all [FiniteCore.bit2]

def storedRow {n : ℕ} (T : Dense.Table n) (t : Fin T.rows) : Row :=
  (decide (T.support.rhs t = 1), List.ofFn (fun k => decide (T.support.matrix t k = 1)))

theorem selected_bit {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows)
    (j : Fin (n + 1)) (hj : T.support.matrix r j = 1) (m : SamplePrograms.Mask) :
    ConstraintRewrite.selectedBit (context T r j, m) =
      Constraint.selectedBit T.support r j (assignment n m) := by
  apply bitValue_injective
  have hr : ConstraintRewrite.pivotRow (context T r j) =
      (decide (T.support.rhs r = 1), List.ofFn (fun k => decide (T.support.matrix r k = 1))) :=
    row_store T r
  have hd : FiniteCore.bit2 (DensePrograms.dot
      (ConstraintRewrite.pivotRow (context T r j)).2
      (ConstraintRewrite.before (context T r j, m))) =
        dot (Constraint.tailRow T.support r j) (assignment n m) := by
    rw [hr, before_word, DensePrograms.dot_exact]
    simp only [bit2_residue, FiniteCore.dot_eq]
    simpa [rowDot, TwoTranslate.dot, bitValue] using
      Constraint.selected_row T.support r j hj false (assignment n m)
  change FiniteCore.bit2 (ConstraintRewrite.selectedBit (context T r j, m)) = _
  rw [ConstraintRewrite.selectedBit, bit2_xor, hd, hr]
  simp only [bit2_residue, Constraint.selectedBit, bitValue_residueBit, sub_two]

theorem solve_word {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows)
    (j : Fin (n + 1)) (hj : T.support.matrix r j = 1) (m : SamplePrograms.Mask) :
    ConstraintRewrite.solve (context T r j, m) =
      List.ofFn (FiniteCore.solve T.support r j (assignment n m)) := by
  rw [ConstraintRewrite.solve, DensePrograms.range_map]
  congr 1; funext k
  simp only [FiniteCore.solve_eq, Constraint.solveMap, permute]
  by_cases hkj : k = j
  · subst k
    simp only [context, if_pos rfl, Equiv.swap_apply_right, Fin.cons_zero]
    exact selected_bit T r j hj m
  · have hv : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    simp only [context, if_neg hv]
    erw [before_bit]
    have hzero : Equiv.swap (0 : Fin (n + 1)) j k ≠ 0 := by
      intro h
      have he := (Equiv.swap (0 : Fin (n + 1)) j).injective
        (h.trans (Equiv.swap_apply_right 0 j).symm)
      exact hkj he
    generalize Equiv.swap (0 : Fin (n + 1)) j k = t at *
    cases t using Fin.cases with
    | zero => exact False.elim (hzero rfl)
    | succ t => rfl

theorem phase_sample {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows)
    (j : Fin (n + 1)) (hj : T.support.matrix r j = 1) (m : SamplePrograms.Mask) :
    ConstraintRewrite.phaseSample (context T r j) m =
      FiniteCore.phase T.phase (FiniteCore.solve T.support r j (assignment n m)) := by
  unfold ConstraintRewrite.phaseSample
  rw [solve_word T r j hj]
  exact phaseValue_store T _

theorem phase_table {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows)
    (j : Fin (n + 1)) (hj : T.support.matrix r j = 1) :
    (ConstraintRewrite.value (context T r j)).2.2 =
      storedPhase (FiniteCore.phaseStep T.support T.phase r j) := by
  unfold ConstraintRewrite.value
  have hs : TabulatePhase.value (fun c : ConstraintRewrite.Context => c.1.1 - 1)
      ConstraintRewrite.phaseSample (context T r j) =
        sampled (fun x => FiniteCore.phase T.phase (FiniteCore.solve T.support r j x)) := by
    change TabulatePhase.value (fun _ : ConstraintRewrite.Context => n)
      ConstraintRewrite.phaseSample (context T r j) = _
    simp only [TabulatePhase.value, sampled, phase_sample T r j hj]
  rw [hs]
  dsimp only
  unfold FiniteCore.phaseStep
  exact sampled_eq _ _

theorem regular {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows)
    (j : Fin (n + 1)) (hj : T.support.matrix r j = 1) :
    Regular (ConstraintRewrite.value (context T r j)) := by
  have hr : ∀ row ∈ (ConstraintRewrite.value (context T r j)).2.1, row.2.length = n := by
    intro row hrow
    simpa [context, store] using ConstraintRewrite.row_width (context T r j) row hrow
  have he : ConstraintRewrite.value (context T r j) =
      (n, (ConstraintRewrite.value (context T r j)).2.1,
        storedPhase (FiniteCore.phaseStep T.support T.phase r j)) :=
    Prod.ext (by simp [ConstraintRewrite.value, context, store]) (Prod.ext rfl (phase_table T r j hj))
  rw [he]
  exact stored_regular _ hr _

theorem support_sample {n : ℕ} (T : Dense.Table (n + 1)) (r t : Fin T.rows)
    (j : Fin (n + 1)) (hj : T.support.matrix r j = 1) (m : SamplePrograms.Mask) :
    FiniteCore.bit2 (ConstraintRewrite.supportSample (context T r j, storedRow T t) m) =
      FiniteCore.dot (T.support.matrix t) (FiniteCore.solve T.support r j (assignment n m)) := by
  unfold ConstraintRewrite.supportSample storedRow
  rw [solve_word T r j hj, DensePrograms.dot_exact]
  simp only [bit2_residue]

theorem support_row {n : ℕ} (T : Dense.Table (n + 1)) (r t : Fin T.rows)
    (j : Fin (n + 1)) (hj : T.support.matrix r j = 1) :
    ConstraintRewrite.supportRow (context T r j, storedRow T t) =
      (decide ((FiniteCore.supportStep T.support r j).rhs t = 1),
        List.ofFn (fun k => decide ((FiniteCore.supportStep T.support r j).matrix t k = 1))) := by
  apply Prod.ext
  · apply bit2_injective
    change FiniteCore.bit2 (Bool.xor (decide (T.support.rhs t = 1))
      (ConstraintRewrite.supportSample (context T r j, storedRow T t) SamplePrograms.origin)) = _
    rw [bit2_xor, bit2_residue, support_sample T r t j hj]
    simp only [bit2_residue, origin_assignment, FiniteCore.supportStep, sub_two]
    rfl
  · change (List.range n).map (fun k => Bool.xor
      (ConstraintRewrite.supportSample (context T r j, storedRow T t) (SamplePrograms.single k))
      (ConstraintRewrite.supportSample (context T r j, storedRow T t) SamplePrograms.origin)) = _
    rw [DensePrograms.range_map]
    congr 1; funext k
    apply bit2_injective
    rw [bit2_xor, support_sample T r t j hj, support_sample T r t j hj]
    simp only [bit2_residue, single_assignment, origin_assignment, FiniteCore.supportStep, sub_two]
    rfl

/-- Complete concrete constraint-table update, including rhs, all columns,
and the materialized quadratic sample table, agrees with the finite kernel. -/
theorem value_store {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows)
    (j : Fin (n + 1)) (hj : T.support.matrix r j = 1) :
    ConstraintRewrite.value (context T r j) = store (FiniteCore.pivotStep T r j) := by
  apply Prod.ext
  · simp [ConstraintRewrite.value, context, store, FiniteCore.pivotStep]
  · apply Prod.ext
    · change (List.ofFn (storedRow T)).map (fun row =>
        ConstraintRewrite.supportRow (context T r j, row)) = _
      rw [List.map_ofFn]
      simp only [support_row T r _ j hj, store, FiniteCore.pivotStep, Dense.support_snapshot, Function.comp_def, Dense.Table.support, Dense.snapshot,
        List.Vector.get_ofFn, Fin.cast_refl, id_eq]
      rfl
    · rw [phase_table T r j hj]
      simp [storedPhase, store, FiniteCore.pivotStep, Dense.snapshot, Function.comp_def]

end Holant.LocalDrafts.Tractability.AffineMachine.ConstraintRefinement
