import Holant.Proofs.LinearProgramming.Foundation.InputBounds
import Mathlib.Tactic.FieldSimp

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
An explicit always-feasible phase-I lifting and its exact zero-objective
recovery. The initial auxiliary point is calculated from A,b, not supplied.
This is a proved phase-I formulation and initial step, NOT a polynomial
optimizer. No ellipsoid volume, precision or termination claim is made here.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.PhaseOne
open Codec Holant.Complexity
open scoped BigOperators

def scale (d : Raw) : ℕ := 2 ^ InputBounds.size d

theorem scale_pos (d : Raw) : 0 < scale d := by unfold scale; positivity

theorem rhs_bound (d : Raw) (i : Fin d.rowCount) : |(d.constant i : ℚ)| ≤ (scale d : ℚ) := by
  have hr : (rowEncoding.encode d.rhs).length ≤ InputBounds.size d := by
    rw [InputBounds.length_formula]; omega
  have hl : (IntegerArithmetic.encoding.encode (d.constant i)).length ≤ InputBounds.size d := by
    unfold Raw.constant
    by_cases hi : i.val < d.rhs.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact (GraphPreprocessing.OriginalCoefficient.ContextFlatMap.member_length
        IntegerArithmetic.encoding d.rhs _ (List.getElem_mem hi)).trans hr
    · rw [List.getD_eq_default _ _ (by omega : d.rhs.length ≤ i.val)]
      change 0 ≤ InputBounds.size d
      omega
  have hb := (InputBounds.integer_magnitude (d.constant i)).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hl)
  have hbq : ((d.constant i).natAbs : ℚ) ≤ (scale d : ℚ) := by
    unfold scale
    exact_mod_cast hb
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hbq

@[ext] structure Point (d : Raw) where
  original : Fin d.dimension → ℚ
  positive : Fin d.rowCount → ℚ
  negative : Fin d.rowCount → ℚ
  slackPositive : Fin d.rowCount → ℚ
  slackNegative : Fin d.rowCount → ℚ
  objective : ℚ

def Feasible (d : Raw) (p : Point d) : Prop :=
  (∀ j, 0 ≤ p.original j ∧ p.original j ≤ 1) ∧
  (∀ i, 0 ≤ p.positive i ∧ p.positive i ≤ 1 ∧
    0 ≤ p.negative i ∧ p.negative i ≤ 1 ∧
    0 ≤ p.slackPositive i ∧ p.slackPositive i ≤ 1 ∧
    0 ≤ p.slackNegative i ∧ p.slackNegative i ≤ 1) ∧
  0 ≤ p.objective ∧ p.objective ≤ 1 ∧
  (∀ i, (∑ j, (d.coefficient i j : ℚ)*p.original j) - (d.constant i : ℚ) =
    (scale d : ℚ)*(p.positive i-p.negative i)) ∧
  (∀ i, p.positive i+p.slackPositive i=p.objective) ∧
  (∀ i, p.negative i+p.slackNegative i=p.objective)

def start (d : Raw) : Point d where
  original := fun _ => 0
  positive := fun i => max (-(d.constant i : ℚ)) 0 / (scale d : ℚ)
  negative := fun i => max (d.constant i : ℚ) 0 / (scale d : ℚ)
  slackPositive := fun i => 1-max (-(d.constant i : ℚ)) 0 / (scale d : ℚ)
  slackNegative := fun i => 1-max (d.constant i : ℚ) 0 / (scale d : ℚ)
  objective := 1

theorem start_feasible (d : Raw) : Feasible d (start d) := by
  have hM : (0 : ℚ) < scale d := by exact_mod_cast scale_pos d
  have hu (i : Fin d.rowCount) :
      0 ≤ max (-(d.constant i : ℚ)) 0/(scale d : ℚ) ∧
      max (-(d.constant i : ℚ)) 0/(scale d : ℚ) ≤ 1 := by
    refine ⟨div_nonneg (le_max_right _ _) hM.le,(div_le_iff₀ hM).mpr ?_⟩
    have hb := (abs_le.mp (rhs_bound d i)).1
    apply max_le <;> linarith
  have hv (i : Fin d.rowCount) :
      0 ≤ max (d.constant i : ℚ) 0/(scale d : ℚ) ∧
      max (d.constant i : ℚ) 0/(scale d : ℚ) ≤ 1 := by
    refine ⟨div_nonneg (le_max_right _ _) hM.le,(div_le_iff₀ hM).mpr ?_⟩
    have hb := (abs_le.mp (rhs_bound d i)).2
    apply max_le <;> linarith
  refine ⟨by intro j; norm_num [start],?_,by norm_num [start],by norm_num [start],?_,?_,?_⟩
  · intro i
    have hu' := hu i
    have hv' := hv i
    dsimp [start]
    exact ⟨hu'.1,hu'.2,hv'.1,hv'.2,by linarith,by linarith,by linarith,by linarith⟩
  · intro i
    have he : max (-(d.constant i : ℚ)) 0 - max (d.constant i : ℚ) 0 = -(d.constant i : ℚ) := by
      by_cases h : 0 ≤ (d.constant i : ℚ)
      · rw [max_eq_right (neg_nonpos.mpr h),max_eq_left h]; ring
      · rw [max_eq_left (by linarith),max_eq_right (by linarith)]; ring
    simp only [start,mul_zero,Finset.sum_const_zero,zero_sub]
    rw [← sub_div,he]
    field_simp [ne_of_gt hM]
  · intro i; dsimp [start]; ring
  · intro i; dsimp [start]; ring

def embed (d : Raw) (x : Fin d.dimension → ℚ) : Point d :=
  ⟨x,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0,0⟩

theorem embed_feasible (d : Raw) (x : Fin d.dimension → ℚ) (hx : Codec.Feasible d x) :
    Feasible d (embed d x) := by
  refine ⟨hx.2,?_,by norm_num [embed],by norm_num [embed],?_,?_,?_⟩
  · intro i; norm_num [embed]
  · intro i; simp [embed,hx.1 i]
  · intro i; simp only [embed,add_zero]
  · intro i; simp only [embed,add_zero]

theorem recover_zero (d : Raw) (p : Point d) (hp : Feasible d p) (ht : p.objective=0) :
    Codec.Feasible d p.original := by
  refine ⟨?_,hp.1⟩
  intro i
  have hb := hp.2.1 i
  have hu := hp.2.2.2.2.2.1 i
  have hv := hp.2.2.2.2.2.2 i
  have hu0 : p.positive i=0 := by rw [ht] at hu; linarith [hb.1,hb.2.2.2.2.1]
  have hv0 : p.negative i=0 := by rw [ht] at hv; linarith [hb.2.2.1,hb.2.2.2.2.2.2.1]
  have he := hp.2.2.2.2.1 i
  rw [hu0,hv0] at he
  linarith

theorem zero_iff (d : Raw) : (∃ p, Feasible d p ∧ p.objective=0) ↔ ∃ x, Codec.Feasible d x := by
  constructor
  · rintro ⟨p,hp,ht⟩; exact ⟨p.original,recover_zero d p hp ht⟩
  · rintro ⟨x,hx⟩; exact ⟨embed d x,embed_feasible d x hx,rfl⟩

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.PhaseOne
