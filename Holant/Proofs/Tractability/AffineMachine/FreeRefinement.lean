import Holant.Proofs.Tractability.AffineMachine.ReadRefinement
import Holant.Proofs.Tractability.AffineMachine.FreeRewrite


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.AffineMachine.FreeRefinement

open Holant.Tractable AffinePhase TwoTranslate EncodedTable
open SampleRefinement ReadRefinement

theorem neighbors_store {n : ℕ} (T : Dense.Table (n + 1)) :
    FreeRewrite.neighbors (store T) =
      List.ofFn (fun j : Fin n => decide (T.phase.mixed 0 j.succ ≠ 0)) := by
  simp only [FreeRewrite.neighbors, store, Nat.add_sub_cancel, DensePrograms.range_map]
  congr 1; funext j
  exact congrArg (fun a : ZMod 4 => decide (a ≠ 0)) (store_mixed T 0 j.succ)

theorem tailWord_store {n : ℕ} (T : Dense.Table (n + 1)) (m : SamplePrograms.Mask) :
    FreeRewrite.tailWord (store T, m) = List.ofFn (Fin.cons false (assignment n m)) := by
  rw [FreeRewrite.tailWord, DensePrograms.range_map]
  congr 1; funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · simp [assignment]

theorem neighbor_bit {n : ℕ} (Q : QuadraticPhase (n + 1)) (j : Fin n) :
    FiniteCore.bit2 (decide (Q.mixed 0 j.succ ≠ 0)) = FiniteCore.neighbors Q j := by
  by_cases h : Q.mixed 0 j.succ = 0 <;> simp [FiniteCore.neighbors, FiniteCore.bit2, h]

theorem parity_store {n : ℕ} (T : Dense.Table (n + 1)) (m : SamplePrograms.Mask) :
    FiniteCore.bit2 (FreeRewrite.parity (store T, m)) =
      FiniteCore.dot (FiniteCore.neighbors T.phase) (assignment n m) := by
  unfold FreeRewrite.parity
  rw [neighbors_store]
  change FiniteCore.bit2 (DensePrograms.dot _ (DensePrograms.word n m)) = _
  rw [word_eq, DensePrograms.dot_exact]
  simp only [neighbor_bit]

theorem parity_lift {n : ℕ} (T : Dense.Table (n + 1)) (m : SamplePrograms.Mask) :
    FiniteCore.bit4 (FreeRewrite.parity (store T, m)) =
      bitLift (dot (FreePhase.neighbors T.phase) (assignment n m)) := by
  have h := parity_store T m
  rw [FiniteCore.dot_eq] at h
  change FiniteCore.bit2 (FreeRewrite.parity (store T, m)) =
    dot (FreePhase.neighbors T.phase) (assignment n m) at h
  rw [← h]
  cases FreeRewrite.parity (store T, m) <;> decide

theorem sample_store {n : ℕ} (T : Dense.Table (n + 1)) (m : SamplePrograms.Mask) :
    FreeRewrite.sample (store T) m = (FiniteCore.freePhase T.phase).eval (assignment n m) := by
  have ht : DensePrograms.phaseValue (store T, FreeRewrite.tailWord (store T, m)) =
      (FreePhase.tail T.phase).eval (assignment n m) := by
    rw [tailWord_store, phaseValue_store, FiniteCore.phase_eq, FreePhase.eval_cons]
    simp [bitValue]
  have hl : FreeRewrite.headLinear (store T) = T.phase.linear 0 := store_linear T 0
  rw [FreeRewrite.sample, ht, hl]
  have hn01 : (0 : ZMod 4) ≠ 1 := by decide
  have hn02 : (0 : ZMod 4) ≠ 2 := by decide
  have hn03 : (0 : ZMod 4) ≠ 3 := by decide
  have hn12 : (1 : ZMod 4) ≠ 2 := by decide
  have hn13 : (1 : ZMod 4) ≠ 3 := by decide
  have hn23 : (2 : ZMod 4) ≠ 3 := by decide
  rcases fourth_cases (T.phase.linear 0) with h | h | h | h <;>
    simp [hn01, hn02, hn03, hn12, hn13, hn23, Ne.symm hn01, Ne.symm hn02, Ne.symm hn03, Ne.symm hn12, Ne.symm hn13, Ne.symm hn23, FiniteCore.freePhase_eq, FreePhase.nextPhase, h,
      Reconstruction.addParity_eval, parity_lift, sub_eq_add_neg]

theorem phase_table_store {n : ℕ} (T : Dense.Table (n + 1)) :
    (FreeRewrite.value (store T)).2.2 = sampled (FiniteCore.freePhase T.phase).eval := by
  change TabulatePhase.value (fun _ : Data => n) FreeRewrite.sample (store T) = _
  simp only [TabulatePhase.value, sampled, sample_store]

theorem regular_store {n : ℕ} (T : Dense.Table (n + 1)) : Regular (FreeRewrite.value (store T)) := by
  have hdim : (FreeRewrite.value (store T)).1 = n := by simp [FreeRewrite.value, store]
  have rows : ∀ r ∈ (FreeRewrite.value (store T)).2.1, r.2.length = n := by
    intro r hr
    simpa [store] using FreeRewrite.row_width (store T) r hr
  have hx : FreeRewrite.value (store T) =
      (n, (FreeRewrite.value (store T)).2.1, sampled (FiniteCore.freePhase T.phase).eval) := by
    exact Prod.ext hdim (Prod.ext rfl (phase_table_store T))
  rw [hx]
  exact sampled_regular _ rows _ (quadratic_thirdDifference _)

theorem phase_eval_store {n : ℕ} (T : Dense.Table (n + 1)) (x : Word n) :
    DensePrograms.phaseValue (FreeRewrite.value (store T), List.ofFn x) =
      (FiniteCore.freePhase T.phase).eval x := by
  have hx : FreeRewrite.value (store T) =
      (n, (FreeRewrite.value (store T)).2.1, sampled (FiniteCore.freePhase T.phase).eval) := by
    exact Prod.ext (by simp [FreeRewrite.value, store]) (Prod.ext rfl (phase_table_store T))
  have hr : ∀ r ∈ (FreeRewrite.value (store T)).2.1, r.2.length = n := by
    intro r h; simpa [store] using FreeRewrite.row_width (store T) r h
  rw [hx, DensePrograms.phaseValue_exact _ (sampled_regular _ hr _ (quadratic_thirdDifference _))]
  simpa only [DensePrograms.getD_ofFn] using
    sampled_eval _ hr (FiniteCore.freePhase T.phase).eval (quadratic_thirdDifference _) x

/-- The physical free branch resamples even when the old kernel keeps its
tail coefficients. This explicit normalization is therefore part of refinement. -/
def normalized {n : ℕ} (T : Dense.Table (n + 1)) : Dense.Table n :=
  Dense.snapshot (FiniteCore.freeSupport T.phase)
    (FiniteCore.reconstruct (FiniteCore.freePhase T.phase).eval (quadratic_thirdDifference _))

theorem normalized_phase {n : ℕ} (T : Dense.Table (n + 1)) (x : Word n) :
    (normalized T).phase.eval x = (FiniteCore.freePhase T.phase).eval x := by
  simp only [normalized, Dense.phase_snapshot, FiniteCore.reconstruct_eq]
  exact Reconstruction.eval_coefficients _ _ x

theorem support_rows_store {n : ℕ} (T : Dense.Table (n + 1)) :
    FreeRewrite.supportRows (store T) = (store (normalized T)).2.1 := by
  have hl : FreeRewrite.headLinear (store T) = T.phase.linear 0 := store_linear T 0
  have he (j : Fin n) : decide (T.phase.mixed 0 j.succ ≠ 0) =
      decide (FreePhase.neighbors T.phase j = 1) := by
    by_cases h : T.phase.mixed 0 j.succ = 0 <;> simp [FreePhase.neighbors, h]
  let rows (S : AffineSystem n) : List Row := List.ofFn (fun r =>
    (decide (S.rhs r = 1), List.ofFn (fun j => decide (S.matrix r j = 1))))
  have hs (S : AffineSystem n) (Q : QuadraticPhase n) :
      (store (Dense.snapshot S Q)).2.1 = rows S := by
    simp [store, Dense.snapshot, Dense.Table.support, rows]
  rw [normalized, hs, FiniteCore.freeSupport_eq]
  rw [FreeRewrite.supportRows, hl]
  simp only [neighbors_store]
  have hn12 : (1 : ZMod 4) ≠ 2 := by decide
  unfold FreePhase.nextSupport
  split_ifs <;> simp_all [hn12, rows, oneEquation, AffineSystem.unconstrained, List.ofFn_succ, he]

theorem value_store {n : ℕ} (T : Dense.Table (n + 1)) :
    FreeRewrite.value (store T) = store (normalized T) := by
  apply Prod.ext
  · simp [FreeRewrite.value, store]
  · apply Prod.ext
    · exact support_rows_store T
    · rw [phase_table_store, sampled_eq _ (quadratic_thirdDifference _)]
      simp [storedPhase, store, normalized, Dense.snapshot, Function.comp_def]

theorem normalized_value {n : ℕ} (T : Dense.Table (n + 1)) (a : AlgebraicComplex) (x : Word n) :
    ((normalized T).state (a * FreePhase.multiplier (T.phase.linear 0))).value x =
      (FreePhase.eliminate (T.state a)).value x := by
  simp only [State.value, affineFormula, Dense.Table.state, normalized,
    Dense.support_snapshot, Dense.phase_snapshot, FiniteCore.reconstruct_eq,
    Reconstruction.eval_coefficients, FiniteCore.freeSupport_eq, FiniteCore.freePhase_eq,
    FreePhase.eliminate]

theorem partition_store {n : ℕ} (T : Dense.Table (n + 1)) (a : AlgebraicComplex)
    (hp : (PivotPrograms.selected (store T)).1 = false)
    (hb : PivotPrograms.badRows (store T) = false) :
    ((normalized T).state (a * FreePhase.multiplier (T.phase.linear 0))).partition =
      (T.state a).partition := by
  have hp' := no_pivot_store T hp
  have hb' : Constraint.badRow T.support = false := by rwa [badRows_store] at hb
  rw [FreePhase.partition_eliminate (T.state a) hp' hb']
  unfold State.partition
  exact Finset.sum_congr rfl (fun x _ => normalized_value T a x)

end Holant.LocalDrafts.Tractability.AffineMachine.FreeRefinement
