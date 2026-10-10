import Holant.Proofs.LinearProgramming.Optimization.Search.GridPrecision

/-!
The actual original-input rounded trajectory. Its fixed binary grid is not
chosen from a feasible witness. Every round's inverse-size, containment and
rounding premises are discharged by induction, including infeasible inputs.
This establishes mathematical invariants and strict progress for this SAME
rounded program; it does not identify Lean iteration with a physical machine.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RoundedTrajectory
open FactorUpdate Containment
open scoped BigOperators Matrix
noncomputable section

def growth (n k : ℕ) : ℕ := 2*(n+1)*(32*(n+1))^k
def step (d : Codec.Raw) (s : State d.dimension) : State d.dimension :=
  match Separation.separate d s.center with
  | none => s
  | some c => if Separation.normal d c=0 then s else
      RoundedGeometry.value (update s (Separation.normal d c))
        (GridPrecision.grid d) (RoundingDeterminant.eta d.dimension)
def run (d : Codec.Raw) (k : ℕ) : State d.dimension := (step d)^[k] (start d.dimension)

@[simp] theorem run_zero (d : Codec.Raw) : run d 0=start d.dimension := rfl

theorem run_succ (d : Codec.Raw) (k : ℕ) : run d (k+1)=step d (run d k) :=
  Function.iterate_succ_apply' (step d) k (start d.dimension)

theorem growth_power (n k : ℕ) : growth n k≤2^((n+6)*(k+1)) := by
  have hn : n+1≤2^(n+1) := (Nat.lt_two_pow_self (n := n+1)).le
  have hb : 32*(n+1)≤2^(n+6) := by
    have h := Nat.mul_le_mul_left 32 hn
    simpa only [show n+6=(n+1)+5 by omega,pow_add,show 2^5=32 by norm_num,Nat.mul_comm] using h
  have hinit : 2*(n+1)≤2^(n+6) := (by nlinarith : 2*(n+1)≤32*(n+1)).trans hb
  have h := Nat.mul_le_mul hinit (Nat.pow_le_pow_left hb k)
  change 2*(n+1)*(32*(n+1))^k≤2^((n+6)*(k+1))
  calc
    _ ≤ 2^(n+6)*(2^(n+6))^k := h
    _ = (2^(n+6))^k*2^(n+6) := Nat.mul_comm _ _
    _ = (2^(n+6))^(k+1) := (pow_succ _ _).symm
    _ = 2^((n+6)*(k+1)) := (pow_mul _ _ _).symm

theorem intermediate_budget (d : Codec.Raw) (k : ℕ) (hk : k≤GridPrecision.iterations d) :
    16*(d.dimension+1)*growth d.dimension k≤GridPrecision.inverseBudget d := by
  have hp : 2^((d.dimension+6)*(k+1))≤2^GridPrecision.exponent d :=
    Nat.pow_le_pow_right (by decide : 0<2)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right hk 1))
  exact Nat.mul_le_mul_left _ ((growth_power d.dimension k).trans hp)

theorem eta_le_one (n : ℕ) (hn : 1≤n) : RoundingDeterminant.eta n≤1 := by
  have hN : (1:ℚ)≤n := by exact_mod_cast hn
  unfold RoundingDeterminant.eta
  apply (div_le_one (by positivity)).mpr
  have hp : (1:ℚ)≤(n:ℚ)^3+1 := by
    have : (0:ℚ)≤(n:ℚ)^3 := by positivity
    linarith
  nlinarith

/-- No caller provides a complete trajectory or its rounding specification.
The current inverse bound and every numerical grid premise are proved here.
-/
theorem invariant (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d) :
    (run d k).factor.det≠0 ∧ RegisterGrowth.Bounded (run d k) (growth d.dimension k) ∧
    ∀ x, Thickening.At d (Thickening.epsilon d) x → Contains (run d k) x := by
  revert hk
  induction k with
  | zero =>
    intro hk
    rw [run_zero]
    exact ⟨start_nonsingular _,by simpa only [growth,RegisterGrowth.growth,pow_zero,mul_one]
      using RegisterGrowth.start_bounded d.dimension,start_contains d⟩
  | succ k ih =>
    intro hk
    obtain ⟨hR,hbound,hcontains⟩ := ih (by omega)
    let M : ℚ := growth d.dimension k
    let U : ℚ := 16*((d.dimension:ℚ)+1)*M
    have hM : 0≤M := by dsimp [M]; positivity
    have hU : 0≤U := by dsimp [U]; positivity
    have hu : U≤(GridPrecision.inverseBudget d:ℚ) := by
      have h := intermediate_budget d k (by omega)
      dsimp only [U,M]
      push_cast at h ⊢
      exact_mod_cast h
    obtain ⟨hsmall,hcover,hdelta,hdet⟩ := GridPrecision.adequate d hn U hU hu
    have he := (RoundingDeterminant.eta_pos d.dimension (by omega)).le
    have he1 := eta_le_one d.dimension (by omega)
    have hh := GridPrecision.grid_pos d
    have hm : M≤32*((d.dimension:ℚ)+1)*M := by
      nlinarith [show (0:ℚ)≤d.dimension by positivity]
    have hnext : (growth d.dimension (k+1):ℚ)=2*U := by
      dsimp only [U,M]
      simp only [growth,pow_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow]
      ring
    rw [run_succ]
    cases hc : Separation.separate d (run d k).center with
    | none =>
      simp only [step,hc]
      refine ⟨hR,?_,hcontains⟩
      apply RegisterGrowth.bounded_mono _ hbound
      rw [hnext]
      dsimp [U]
      nlinarith
    | some c =>
      by_cases hg : Separation.normal d c=0
      · simp only [step,hc,if_pos hg]
        refine ⟨hR,?_,hcontains⟩
        apply RegisterGrowth.bounded_mono _ hbound
        rw [hnext]
        dsimp [U]
        nlinarith
      · simp only [step,hc,if_neg hg]
        let s := update (run d k) (Separation.normal d c)
        have hsR := (actual_cut_progress d hn _ c hR hg).1
        have hsbound : RegisterGrowth.Bounded s U := RegisterGrowth.update_bounded hn _ _ hR hg M hM hbound
        have hscontains := actual_cut_contains d hn _ c hR hc hg hcontains
        refine ⟨RoundedGeometry.nonsingular s _ hh _ U he hU hsR hsbound.2.2 hsmall,?_,?_⟩
        · rw [hnext]
          exact RoundedGeometry.bounded s _ hh _ U he he1 hU hsR hsbound hsmall
        · intro x hx
          exact RoundedGeometry.contains (by omega) s _ hh _ U he hU hsR hsbound.2.2
            hsmall hcover x (hscontains x hx)

theorem active_progress (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (hk : k<GridPrecision.iterations d) (c : Separation.Constraint d)
    (hc : Separation.separate d (run d k).center=some c) (hg : Separation.normal d c≠0) :
    |(run d (k+1)).factor.det|≤|(run d k).factor.det| * RoundingDeterminant.contraction d.dimension := by
  obtain ⟨hR,hbound,hcontains⟩ := invariant d hn k hk.le
  let M : ℚ := growth d.dimension k
  let U : ℚ := 16*((d.dimension:ℚ)+1)*M
  have hM : 0≤M := by dsimp [M]; positivity
  have hU : 0≤U := by dsimp [U]; positivity
  have hu : U≤(GridPrecision.inverseBudget d:ℚ) := by
    dsimp only [U,M]
    push_cast
    exact_mod_cast intermediate_budget d k hk.le
  obtain ⟨hsmall,hcover,hdelta,hdet⟩ := GridPrecision.adequate d hn U hU hu
  let s := update (run d k) (Separation.normal d c)
  have hsR := (actual_cut_progress d hn _ c hR hg).1
  have hsbound : RegisterGrowth.Bounded s U := RegisterGrowth.update_bounded hn _ _ hR hg M hM hbound
  have hround := RoundingDeterminant.rounded_det (by omega : 0<d.dimension) s _ (GridPrecision.grid_pos d)
    hsR U hU hsbound.2.2 hdelta hdet
  have hstep := (actual_cut_progress d hn _ c hR hg).2
  rw [run_succ,step,hc]
  dsimp only
  rw [if_neg hg]
  calc
    _ ≤ |s.factor.det| * (1+RoundingDeterminant.loss d.dimension/8)^2 := hround
    _ ≤ (|(run d k).factor.det| * Scales.contraction d.dimension)*
        (1+RoundingDeterminant.loss d.dimension/8)^2 :=
      mul_le_mul_of_nonneg_right hstep (sq_nonneg _)
    _ = |(run d k).factor.det| * (Scales.contraction d.dimension*
        (1+RoundingDeterminant.loss d.dimension/8)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (RoundingDeterminant.total_contraction _) (abs_nonneg _)

theorem accepted (d : Codec.Raw) (k : ℕ)
    (h : Separation.separate d (run d k).center=none) : ∃ x, Codec.Feasible d x :=
  (Thickening.nonempty_iff d).mp ⟨_,(Separation.none_iff d _).mp h⟩

theorem rejected_zero (d : Codec.Raw) (k : ℕ) (c : Separation.Constraint d)
    (hc : Separation.separate d (run d k).center=some c) (hg : Separation.normal d c=0) :
    ¬∃ x, Codec.Feasible d x := Separation.zero_cut_reject d _ c hc hg

theorem accepted_fixed (d : Codec.Raw) (k t : ℕ)
    (h : Separation.separate d (run d k).center=none) : run d (k+t)=run d k := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hr : run d (k+(t+1))=step d (run d (k+t)) := by
      simpa only [Nat.add_assoc] using run_succ d (k+t)
    rw [hr,ih]
    simp only [step,h]

theorem target_inverse_entry (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d) (hf : ∃ x, Codec.Feasible d x) (i j : Fin d.dimension) :
    |(run d k).factor⁻¹ i j|≤(2^(RadiusBudget.exponent d+1):ℕ) := by
  obtain ⟨x,hx⟩ := hf
  obtain ⟨hR,hbound,hcontains⟩ := invariant d hn k hk
  have hr := Thickening.radius_pos d
  have hbase : Contains (run d k) x :=
    hcontains x (InverseBounds.inner_full d x x hx (fun l => by simp [hr.le]))
  have hperturb : Contains (run d k) (x+Pi.single j (Thickening.radius d)) := by
    apply hcontains
    apply InverseBounds.inner_full d x _ hx
    intro l
    by_cases hl : l=j
    · subst l
      simp [abs_of_pos hr]
    · simp [Pi.single_apply,hl,Ne.symm hl,hr.le]
  have hb := InverseBounds.inverse_entry (run d k) x (Thickening.radius d) hr hR hbase j hperturb i
  have hpow : (0:ℚ)<(2^RadiusBudget.exponent d:ℕ) := by positivity
  have hinv : 1/Thickening.radius d≤((2^RadiusBudget.exponent d:ℕ):ℚ) := by
    have h := one_div_le_one_div_of_le (by positivity : (0:ℚ)<1/(2^RadiusBudget.exponent d:ℕ))
      (RadiusBudget.radius_lower d)
    simpa only [one_div_one_div] using h
  calc
    _ ≤ 2/Thickening.radius d := hb
    _ ≤ 2*((2^RadiusBudget.exponent d:ℕ):ℚ) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℚ)≤2)
    _ = _ := by simp [pow_succ]; ring

theorem target_det_lower (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d) (hf : ∃ x, Codec.Feasible d x) :
    1/((2^InverseBounds.exponent d:ℕ):ℚ)≤|(run d k).factor.det| := by
  have hm := Matrix.det_le (A := (run d k).factor⁻¹) (abv := AbsoluteValue.abs)
    (target_inverse_entry d hn k hk hf)
  have hp := DeterminantGap.bound_le_power d.dimension (2^(RadiusBudget.exponent d+1))
    (RadiusBudget.exponent d+1) le_rfl
  have hp' : ((DeterminantGap.bound d.dimension (2^(RadiusBudget.exponent d+1)):ℕ):ℚ)≤
      ((2^InverseBounds.exponent d:ℕ):ℚ) := by exact_mod_cast hp
  have hb : |(run d k).factor⁻¹.det|≤((2^InverseBounds.exponent d:ℕ):ℚ) :=
    (by simpa [Fintype.card_fin,nsmul_eq_mul,DeterminantGap.bound] using hm :
      |(run d k).factor⁻¹.det| ≤
        (DeterminantGap.bound d.dimension (2^(RadiusBudget.exponent d+1)):ℚ)).trans hp'
  have he := Matrix.det_nonsing_inv_mul_det (run d k).factor
    (isUnit_iff_ne_zero.mpr (invariant d hn k hk).1)
  have hid : |(run d k).factor⁻¹.det| * |(run d k).factor.det|=1 := by
    rw [← abs_mul,he]
    norm_num
  have hmul := mul_le_mul_of_nonneg_right hb (abs_nonneg (run d k).factor.det)
  rw [hid] at hmul
  apply (div_le_iff₀ (by positivity : (0:ℚ)<(2^InverseBounds.exponent d:ℕ))).mpr
  simpa only [mul_comm] using hmul

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RoundedTrajectory
