import Holant.Proofs.Tractability.AffineMachine.ReadRefinement


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.AffineMachine.SparseRefinement

open Holant.Tractable AffinePhase TwoTranslate EncodedTable
open scoped BigOperators

def coefficient (indices : List ℕ) (j : ℕ) : ZMod 2 :=
  (indices.map (fun k => if k = j then (1 : ZMod 2) else 0)).sum

theorem row_coefficient (n : ℕ) (r : RawBlocks.Row) (j : Fin n) :
    FiniteCore.bit2 ((BlockAggregation.row n r).2.getD j.val false) = coefficient r.2 j.val := by
  simp only [BlockAggregation.row, DensePrograms.range_map, DensePrograms.getD_ofFn]
  rw [SamplePrograms.parity, ResidueCells.parity_value]
  simp [coefficient, List.map_map, SamplePrograms.at, SamplePrograms.single, FiniteCore.bit2, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro k hk
  by_cases h : k = j.val <;> simp [h, eq_comm, SamplePrograms.at, FiniteCore.bit2]

theorem single_sum {n : ℕ} (i : ℕ) (x : Word n) :
    (∑ j : Fin n, (if i = j.val then (1 : ZMod 2) else 0) * bitValue (ZMod 2) (x j)) =
      FiniteCore.bit2 ((List.ofFn x).getD i false) := by
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    have hget : (List.ofFn x).getD i false = x j := DensePrograms.getD_ofFn x j false
    rw [hget]
    rw [Finset.sum_eq_single j]
    · simp [j, FiniteCore.bit2, bitValue]
    · intro k hk hne
      have hn : i ≠ k.val := by
        intro h
        apply hne
        exact Fin.ext h.symm
      simp [hn]
    · simp
  · have hn (j : Fin n) : i ≠ j.val := by intro h; have hj := j.isLt; omega
    have hget : (List.ofFn x).getD i false = false :=
      List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)
    simp [hn, hi, hget, FiniteCore.bit2]

theorem coefficient_dot {n : ℕ} (indices : List ℕ) (x : Word n) :
    (∑ j : Fin n, coefficient indices j.val * bitValue (ZMod 2) (x j)) =
      (indices.map (fun k => FiniteCore.bit2 ((List.ofFn x).getD k false))).sum := by
  induction indices with
  | nil => simp [coefficient]
  | cons k ks ih =>
    have hc (j : Fin n) : coefficient (k :: ks) j.val =
        (if k = j.val then 1 else 0) + coefficient ks j.val := by simp [coefficient]
    simp only [hc, add_mul, Finset.sum_add_distrib, single_sum, ih, List.map_cons, List.sum_cons]

theorem row_dot (n : ℕ) (r : RawBlocks.Row) (x : Word n) :
    FiniteCore.dot (fun j => FiniteCore.bit2 ((BlockAggregation.row n r).2.getD j.val false)) x =
      (r.2.map (fun k => FiniteCore.bit2 ((List.ofFn x).getD k false))).sum := by
  simp only [FiniteCore.dot_eq, TwoTranslate.dot, row_coefficient]
  exact coefficient_dot r.2 x

theorem row_holds (n : ℕ) (r : RawBlocks.Row) (x : Word n) :
    FiniteCore.dot (fun j => FiniteCore.bit2 ((BlockAggregation.row n r).2.getD j.val false)) x =
        FiniteCore.bit2 (BlockAggregation.row n r).1 ↔
      RawBlocks.rowHolds (fun k => (List.ofFn x).getD k false) r := by
  rw [row_dot]
  rfl

theorem support_holds {s b : ℕ} (input : BlockAggregation.Input (s := s) (b := b))
    (x : Word input.1) :
    (support (BlockAggregation.value input).1).Holds x ↔
      ∀ r ∈ BlockAggregation.supportRows input.2,
        RawBlocks.rowHolds (fun k => (List.ofFn x).getD k false) r := by
  let rs := BlockAggregation.supportRows input.2
  change (∀ i : Fin (rs.map (BlockAggregation.row input.1)).length,
    (∑ j, FiniteCore.bit2 (((rs.map (BlockAggregation.row input.1)).get i).2.getD j.val false) *
      bitValue (ZMod 2) (x j)) = FiniteCore.bit2 ((rs.map (BlockAggregation.row input.1)).get i).1) ↔ _
  constructor
  · intro h r hr
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
    have hh := h ⟨i.val, by simpa only [rs, List.length_map] using i.isLt⟩
    have he : (rs.map (BlockAggregation.row input.1)).get ⟨i.val, by simpa only [rs, List.length_map] using i.isLt⟩ =
        BlockAggregation.row input.1 r := by simp [rs, ← hi, List.get_eq_getElem]
    rw [he] at hh
    exact (row_holds input.1 r x).mp (by simpa only [FiniteCore.dot_eq, TwoTranslate.dot] using hh)
  · intro h i
    let j : Fin rs.length := ⟨i.val, by simpa only [rs, List.length_map] using i.isLt⟩
    have hh := (row_holds input.1 (rs.get j) x).mpr (h _ (List.get_mem rs j))
    simpa only [FiniteCore.dot_eq, TwoTranslate.dot, List.get_eq_getElem, List.getElem_map] using hh

end Holant.LocalDrafts.Tractability.AffineMachine.SparseRefinement
