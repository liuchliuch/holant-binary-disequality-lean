import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.RankIncrease
import Holant.Proofs.LinearProgramming.Foundation.ThresholdProgram

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Unconditional positive-coordinate threshold theorem from original A,b. The
basic point and its active subsystem are derived inside the proof. No feasible
point, basis, optimum, positive epsilon or solver is an extra input. This is a
reduction to bounded feasibility, not a bounded-feasibility algorithm.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.PositiveThreshold
open Codec BasicPoint
noncomputable section

theorem witness_gap (d : Raw) (j : Fin d.dimension) (h : Positive d j) :
    ∃ x, Feasible d x ∧ 1/(InputBounds.denominator d : ℚ) ≤ x j := by
  obtain ⟨x,hx,hj⟩ := h
  obtain ⟨y,hy,hxy,hr⟩ := exists_rigid_above d j x hx
  obtain ⟨select,ha,hd⟩ := exists_basis d y hr
  have he := basis_system d y hy select ha
  have hp : 0 < y j := hj.trans_le hxy
  have hg := DeterminantGap.positive_gap (InputBounds.matrix d select)
    (fun i => rightSide d y (select i)) y he hd j hp
  have hb := InputBounds.determinant_bound d select
  have hdet : ((InputBounds.matrix d select).det : ℚ) ≠ 0 := by exact_mod_cast hd
  have hD : (0 : ℚ) < InputBounds.denominator d := by
    exact_mod_cast InputBounds.denominator_pos d
  refine ⟨y,hy,(div_le_iff₀ hD).mpr ?_⟩
  exact ((div_le_iff₀ (abs_pos.mpr hdet)).mp hg).trans
    (mul_le_mul_of_nonneg_left hb hp.le)

theorem positive_iff_gap (d : Raw) (j : Fin d.dimension) :
    Positive d j ↔ ∃ x, Feasible d x ∧ 1/(InputBounds.denominator d : ℚ) ≤ x j := by
  refine ⟨witness_gap d j,?_⟩
  rintro ⟨x,hx,hj⟩
  have hD : (0 : ℚ) < InputBounds.denominator d := by
    exact_mod_cast InputBounds.denominator_pos d
  exact ⟨x,hx,(one_div_pos.mpr hD).trans_le hj⟩

theorem positive_iff_threshold (d : Raw) (j : Fin d.dimension) :
    Positive d j ↔ ∃ y, Feasible (Threshold.value d j (InputBounds.denominator d)).val y := by
  rw [positive_iff_gap]
  exact (Threshold.exists_iff d j _ (InputBounds.denominator_pos d)).symm

theorem positive_iff_program (d : Input) (j : Fin d.val.dimension) :
    Positive d.val j ↔ ∃ y,
      Feasible (ThresholdProgram.value (⟨d,j⟩,InputBounds.denominator d.val)).val y := by
  rw [positive_iff_gap]
  exact (ThresholdProgram.exists_iff d j _ (InputBounds.denominator_pos d.val)).symm

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.PositiveThreshold
