import Holant.Proofs.LinearProgramming.Optimization.Search.RoundedTrajectory

/-!
Budget correctness for the actual rounded trajectory in dimensions ≥2.
The numerical budget and fixed grid come ONLY from the original Raw input.
Feasible inputs cannot exhaust the budget without acceptance: the derived
inner box forces a determinant lower bound contradicted by real progress.
No all-rounds size/progress certificate is an input. StepProgram and
Complexity.CounterLoop connect this semantic finite search to the physical loop.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RoundedTermination
open FactorUpdate Containment
open Holant.Complexity.GraphPreprocessing
noncomputable section

def block (n : ℕ) : ℕ := 4*(n^3+1)
def value (d : Codec.Raw) : Bool :=
  decide (Separation.separate d (RoundedTrajectory.run d (GridPrecision.iterations d)).center=none)

theorem block_halves (n : ℕ) : RoundingDeterminant.contraction n^block n≤1/2 := by
  let r := RoundingDeterminant.contraction n
  have hr : 0<r := RoundingDeterminant.contraction_pos n
  have hr1 : r<1 := RoundingDeterminant.contraction_lt_one n
  have hne : r≠0 := ne_of_gt hr
  have hkr : (block n:ℚ)*(1-r)=1 := by
    unfold block r RoundingDeterminant.contraction RoundingDeterminant.loss
    push_cast
    have h : (n:ℚ)^3+1≠0 := ne_of_gt (by positivity : (0:ℚ)<(n:ℚ)^3+1)
    field_simp [h]
    <;> ring
  have hinv : 1≤r⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hr1.le)
  have he : (block n:ℚ)*(r⁻¹-1)=r⁻¹ := by
    have he' : r⁻¹-1=(1-r)/r := by field_simp [hne] <;> ring
    rw [he',← mul_div_assoc,hkr,one_div]
  have hb := one_add_mul_le_pow (show (-2:ℚ)≤r⁻¹-1 by linarith) (block n)
  rw [add_sub_cancel,he] at hb
  have hp := pow_nonneg hr.le (block n)
  have hm := mul_le_mul_of_nonneg_right hb hp
  rw [← mul_pow,inv_mul_cancel₀ hne,one_pow] at hm
  have ht := (mul_le_mul_of_nonneg_right (by linarith : (2:ℚ)≤1+r⁻¹) hp).trans hm
  exact (le_div_iff₀ (by norm_num : (0:ℚ)<2)).mpr (by nlinarith [ht])

theorem budget_decay (d : Codec.Raw) :
    RoundingDeterminant.contraction d.dimension^GridPrecision.iterations d≤
      1/((2^BudgetTermination.blocks d:ℕ):ℚ) := by
  have hN : GridPrecision.iterations d=block d.dimension*BudgetTermination.blocks d := by
    unfold GridPrecision.iterations BudgetTermination.iterations Decay.block block
    ring
  rw [hN,pow_mul]
  have h := pow_le_pow_left₀ (pow_nonneg (RoundingDeterminant.contraction_pos _).le _)
    (block_halves d.dimension) (BudgetTermination.blocks d)
  simpa only [div_pow,one_pow,Nat.cast_pow,Nat.cast_ofNat] using h

theorem active_prefix (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d)
    (ha : ∀ i<k, ∃ c, Separation.separate d (RoundedTrajectory.run d i).center=some c ∧
      Separation.normal d c≠0) :
    |(RoundedTrajectory.run d k).factor.det|≤
      |(start d.dimension).factor.det| * RoundingDeterminant.contraction d.dimension^k := by
  revert hk ha
  induction k with
  | zero => intro hk ha; simp [RoundedTrajectory.run]
  | succ k ih =>
    intro hk ha
    obtain ⟨c,hc,hg⟩ := ha k (by omega)
    have hs := RoundedTrajectory.active_progress d hn k (by omega) c hc hg
    have hp := ih (by omega) (fun i hi => ha i (by omega))
    calc
      _ ≤ |(RoundedTrajectory.run d k).factor.det| * RoundingDeterminant.contraction d.dimension := hs
      _ ≤ (|(start d.dimension).factor.det| * RoundingDeterminant.contraction d.dimension^k)*
          RoundingDeterminant.contraction d.dimension :=
        mul_le_mul_of_nonneg_right hp (RoundingDeterminant.contraction_pos _).le
      _ = _ := by rw [pow_succ]; ring

theorem feasible_active (d : Codec.Raw) (hf : ∃ x, Codec.Feasible d x)
    (hN : Separation.separate d (RoundedTrajectory.run d (GridPrecision.iterations d)).center≠none)
    (i : ℕ) (hi : i<GridPrecision.iterations d) :
    ∃ c, Separation.separate d (RoundedTrajectory.run d i).center=some c ∧ Separation.normal d c≠0 := by
  cases hc : Separation.separate d (RoundedTrajectory.run d i).center with
  | none =>
    have hr := RoundedTrajectory.accepted_fixed d i (GridPrecision.iterations d-i) hc
    rw [Nat.add_sub_of_le hi.le] at hr
    exact (hN (by simpa only [hr] using hc)).elim
  | some c =>
    refine ⟨c,rfl,?_⟩
    intro hz
    exact RoundedTrajectory.rejected_zero d i c hc hz hf

theorem budget_accepts (d : Codec.Raw) (hn : 2≤d.dimension) (hf : ∃ x, Codec.Feasible d x) :
    Separation.separate d (RoundedTrajectory.run d (GridPrecision.iterations d)).center=none := by
  by_contra hN
  have hl := RoundedTrajectory.target_det_lower d hn (GridPrecision.iterations d) le_rfl hf
  have hu := active_prefix d hn (GridPrecision.iterations d) le_rfl (feasible_active d hf hN)
  have hinit := BudgetTermination.start_det_bound d.dimension
  have hdec := budget_decay d
  have hupper : |(RoundedTrajectory.run d (GridPrecision.iterations d)).factor.det|≤
      ((2^BudgetTermination.outerExponent d.dimension:ℕ):ℚ)/((2^BudgetTermination.blocks d:ℕ):ℚ) := by
    calc
      _ ≤ |(start d.dimension).factor.det| * RoundingDeterminant.contraction d.dimension^GridPrecision.iterations d := hu
      _ ≤ ((2^BudgetTermination.outerExponent d.dimension:ℕ):ℚ)*(1/((2^BudgetTermination.blocks d:ℕ):ℚ)) :=
        mul_le_mul hinit hdec (pow_nonneg (RoundingDeterminant.contraction_pos _).le _)
          (by positivity)
      _ = _ := by ring
  have houterPos : (0:ℚ)<((2^BudgetTermination.outerExponent d.dimension:ℕ):ℚ) := by positivity
  have hinversePos : (0:ℚ)<((2^InverseBounds.exponent d:ℕ):ℚ) := by positivity
  have hden : (2^BudgetTermination.blocks d:ℕ)=
      2^BudgetTermination.outerExponent d.dimension*2^InverseBounds.exponent d*2 := by
    rw [BudgetTermination.blocks,pow_succ,pow_add]
  have hexact : ((2^BudgetTermination.outerExponent d.dimension:ℕ):ℚ)/((2^BudgetTermination.blocks d:ℕ):ℚ)=
      1/(2*((2^InverseBounds.exponent d:ℕ):ℚ)) := by
    rw [hden,Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat]
    field_simp [ne_of_gt houterPos,ne_of_gt hinversePos]
    <;> ring
  rw [hexact] at hupper
  have hdouble : ((2^InverseBounds.exponent d:ℕ):ℚ)<
      2*((2^InverseBounds.exponent d:ℕ):ℚ) := by linarith
  have hstrict : (1:ℚ)/(2*((2^InverseBounds.exponent d:ℕ):ℚ))<1/((2^InverseBounds.exponent d:ℕ):ℚ) :=
    one_div_lt_one_div_of_lt hinversePos hdouble
  exact (not_le_of_gt hstrict) (hl.trans hupper)

theorem correct (d : Codec.Raw) (hn : 2≤d.dimension) : value d=true ↔ ∃ x, Codec.Feasible d x := by
  simp only [value,decide_eq_true_eq]
  exact ⟨RoundedTrajectory.accepted d _,budget_accepts d hn⟩

theorem physical_count_bound (d : Codec.Input) : GridPrecision.iterations d.val≤
    GridPrecision.countComputes.outputBound.bound.eval (Codec.inputEncoding.encode d).length := by
  simpa only [UnaryBinary.unaryEncoding,List.length_replicate] using GridPrecision.countComputes.outputBound.length_le d

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RoundedTermination
