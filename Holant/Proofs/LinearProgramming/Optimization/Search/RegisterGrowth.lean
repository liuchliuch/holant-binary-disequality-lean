import Holant.Proofs.LinearProgramming.Optimization.Search.Trajectory

/-!
Magnitude and inverse growth for the ACTUAL rational updates, including
infeasible inputs. An explicit inverse column is derived from the delivered
rational preimage, and its entries are uniformly bounded independently of
the cut coefficients. No feasible point, supplied condition number or
all-states bound is an input. These are magnitude bounds, not canonical
denominator bounds, which SignedRound and RoundedGeometry establish after storage rounding.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RegisterGrowth
open FactorUpdate Containment Projection
open scoped BigOperators Matrix
noncomputable section

theorem scales (n : ℕ) (hn : 2≤n) :
    (1/2:ℚ)≤Scales.axial n ∧ Scales.axial n≤1 ∧
    1≤Scales.transverse n ∧ Scales.transverse n≤2 ∧
    1≤Scales.inflation n ∧ Scales.inflation n≤2 := by
  have hN : (2:ℚ)≤n := by exact_mod_cast hn
  have hn2 : (1:ℚ)≤(n:ℚ)^2 := one_le_pow₀ (by linarith)
  have hn4 : (1:ℚ)≤(n:ℚ)^4 := one_le_pow₀ (by linarith)
  have hb : (0:ℚ)≤1/(n:ℚ)^2 := by positivity
  have hb' : (1:ℚ)/(n:ℚ)^2≤1 := (div_le_one (by positivity)).mpr hn2
  have hg : (0:ℚ)≤1/(16*(n:ℚ)^4) := by positivity
  have hg' : (1:ℚ)/(16*(n:ℚ)^4)≤1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  refine ⟨?_,?_,by dsimp [Scales.transverse]; linarith,
    by dsimp [Scales.transverse]; linarith,
    by dsimp [Scales.inflation]; linarith,
    by dsimp [Scales.inflation]; linarith⟩
  · unfold Scales.axial
    apply (le_div_iff₀ (by positivity : (0:ℚ)<(n:ℚ)+1)).mpr
    linarith
  · unfold Scales.axial
    exact (div_le_one (by positivity)).mpr (by linarith)

theorem projection_entry {n : ℕ} (v : Vec n) (hv : v≠0) (i j : Fin n) :
    |v j*v i/square v|≤1 := by
  have hs := square_pos v hv
  have hi : v i^2≤square v :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ i)
  have hj : v j^2≤square v :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j)
  have hb : |v j*v i|≤square v := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|v i|-|v j|),sq_abs (v i),sq_abs (v j)]
  rw [abs_div,abs_of_pos hs]
  exact (div_le_one hs).mpr hb

theorem transform_entry {n : ℕ} (hn : 2≤n) (v : Vec n) (hv : v≠0) (i j : Fin n) :
    transform v i j=Scales.inflation n*
      (Scales.transverse n*(if i=j then 1 else 0)+
        (Scales.axial n-Scales.transverse n)*(v j*v i/square v)) := by
  have hs := ne_of_gt (square_pos v hv)
  have hb := ne_of_gt (Scales.transverse_pos n)
  simp only [transform,shear,Matrix.add_apply,Matrix.smul_apply,Matrix.mul_apply,
    Matrix.replicateCol,Matrix.replicateRow,Matrix.of_apply,Fintype.sum_unique,
    Pi.smul_apply,smul_eq_mul,Matrix.one_apply]
  field_simp [hs,hb]
  <;> ring

theorem transform_entry_bound {n : ℕ} (hn : 2≤n) (v : Vec n) (hv : v≠0) (i j : Fin n) :
    |transform v i j|≤8 := by
  obtain ⟨ha0,ha1,hb0,hb1,hg0,hg1⟩ := scales n hn
  have hab : |Scales.axial n-Scales.transverse n|≤2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hd : |(if i=j then 1 else 0 : ℚ)|≤1 := by split_ifs <;> norm_num
  have hp := projection_entry v hv i j
  rw [transform_entry hn v hv i j,abs_mul,abs_of_nonneg (by linarith : 0≤Scales.inflation n)]
  have hinner : |Scales.transverse n*(if i=j then 1 else 0)+
      (Scales.axial n-Scales.transverse n)*(v j*v i/square v)|≤4 := by
    calc
      _ ≤ |Scales.transverse n*(if i=j then 1 else 0)|+
          |(Scales.axial n-Scales.transverse n)*(v j*v i/square v)| := abs_add_le _ _
      _ ≤ 2*1+2*1 := by
        rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0≤Scales.transverse n)]
        exact add_le_add (mul_le_mul hb1 hd (abs_nonneg _) (by norm_num))
          (mul_le_mul hab hp (abs_nonneg _) (by norm_num))
      _ = 4 := by norm_num
  calc
    _ ≤ 2*4 := mul_le_mul hg1 hinner (abs_nonneg _) (by norm_num)
    _ = 8 := by norm_num

/-- The inverse is used only in proofs. Its action is obtained from two
explicit preimages of the SAME transform, so no inverse oracle is assumed. -/
theorem inverse_action {n : ℕ} (hn : 2≤n) (v y : Vec n) (hv : v≠0) :
    (transform v)⁻¹.mulVec y=preimage v y-preimage v 0 := by
  have hunit : IsUnit (transform v).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (transform_det_pos hn v hv))
  have hm : (transform v).mulVec (preimage v y-preimage v 0)=y := by
    rw [Matrix.mulVec_sub,preimage_maps hn v y hv,preimage_maps hn v 0 hv]
    abel
  have h := congrArg (fun z => (transform v)⁻¹.mulVec z) hm
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hunit,Matrix.one_mulVec] at h
  exact h.symm

theorem inverse_entry {n : ℕ} (hn : 2≤n) (v : Vec n) (hv : v≠0) (i j : Fin n) :
    (transform v)⁻¹ i j=(1/Scales.inflation n)*
      ((1/Scales.transverse n)*(if i=j then 1 else 0)+
        (1/Scales.axial n-1/Scales.transverse n)*(v j*v i/square v)) := by
  have h := congrFun (inverse_action hn v (Pi.single j 1) hv) i
  have hs := ne_of_gt (square_pos v hv)
  have ha := ne_of_gt (Scales.axial_pos n (by omega))
  have hb := ne_of_gt (Scales.transverse_pos n)
  have hg := ne_of_gt (Scales.inflation_pos n)
  simp only [Matrix.mulVec,dotProduct_single,mul_one,Pi.smul_apply,smul_eq_mul,
    preimage,transversePart,Pi.sub_apply,
    Pi.add_apply,dotProduct_single,dotProduct_zero,mul_one,zero_div,Pi.zero_apply,
    Pi.single_apply,eq_comm] at h
  rw [h]
  field_simp
  <;> ring

theorem inverse_entry_bound {n : ℕ} (hn : 2≤n) (v : Vec n) (hv : v≠0) (i j : Fin n) :
    |(transform v)⁻¹ i j|≤4 := by
  obtain ⟨ha0,ha1,hb0,hb1,hg0,hg1⟩ := scales n hn
  have ha : (0:ℚ)<Scales.axial n := Scales.axial_pos n (by omega)
  have hb : (0:ℚ)<Scales.transverse n := Scales.transverse_pos n
  have hg : (0:ℚ)<Scales.inflation n := Scales.inflation_pos n
  have hai : (1:ℚ)/Scales.axial n≤2 := (div_le_iff₀ ha).mpr (by linarith)
  have hbi : (1:ℚ)/Scales.transverse n≤1 := (div_le_one hb).mpr hb0
  have hgi : (1:ℚ)/Scales.inflation n≤1 := (div_le_one hg).mpr hg0
  have hd : |(if i=j then 1 else 0 : ℚ)|≤1 := by split_ifs <;> norm_num
  have hp := projection_entry v hv i j
  have hab : |1/Scales.axial n-1/Scales.transverse n|≤3 := by
    exact (abs_sub _ _).trans (by rw [abs_of_pos (by positivity),abs_of_pos (by positivity)]; linarith)
  rw [inverse_entry hn v hv i j,abs_mul,abs_of_pos (by positivity : (0:ℚ)<1/Scales.inflation n)]
  have hinner : |(1/Scales.transverse n)*(if i=j then 1 else 0)+
      (1/Scales.axial n-1/Scales.transverse n)*(v j*v i/square v)|≤4 := by
    calc
      _ ≤ |(1/Scales.transverse n)*(if i=j then 1 else 0)|+
          |(1/Scales.axial n-1/Scales.transverse n)*(v j*v i/square v)| := abs_add_le _ _
      _ ≤ 1*1+3*1 := by
        rw [abs_mul,abs_mul,abs_of_pos (by positivity : (0:ℚ)<1/Scales.transverse n)]
        exact add_le_add (mul_le_mul hbi hd (abs_nonneg _) (by norm_num))
          (mul_le_mul hab hp (abs_nonneg _) (by norm_num))
      _ = 4 := by norm_num
  calc
    _ ≤ 1*4 := mul_le_mul hgi hinner (abs_nonneg _) (by norm_num)
    _ = 4 := by norm_num

theorem matrix_product {n : ℕ} (A B : Mat n) (a b : ℚ)
    (ha : 0≤a) (hb : 0≤b) (hA : ∀ i j, |A i j|≤a) (hB : ∀ i j, |B i j|≤b)
    (i j : Fin n) : |(A*B) i j|≤(n:ℚ)*a*b := by
  calc
    _ ≤ ∑ k, |A i k*B k j| := by
      simpa only [Matrix.mul_apply] using Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, a*b := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ha
    _ = _ := by simp; ring

theorem normalizer_coordinate {n : ℕ} (hn : 2≤n) (v : Vec n) (hv : v≠0) (i : Fin n) :
    |(shift v • v) i|≤1 := by
  let a := NormApprox.value (square v) (Scales.precision n)
  have ha : 0<a := NormApprox.value_pos _ _ (Scales.precision_pos n (by omega))
  have hb := (NormApprox.bounds (square v) (square_pos v hv)
    (Scales.precision n) (Scales.precision_pos n (by omega))).1
  have hs : square v≤a^2 := by
    have har : (0:ℝ)≤a := by exact_mod_cast ha.le
    have hsr : (0:ℝ)≤square v := by exact_mod_cast square_nonneg v
    have hsq := Real.sq_sqrt hsr
    have hr := Real.sqrt_nonneg (square v:ℝ)
    have : (square v:ℝ)≤(a:ℝ)^2 := by nlinarith
    exact_mod_cast this
  have hi : v i^2≤square v :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ i)
  have hcoord : |v i|≤a := by nlinarith [sq_abs (v i),abs_nonneg (v i)]
  have hd : (0:ℚ)<((n:ℚ)+1)*a := by positivity
  have hm : |v i|≤((n:ℚ)+1)*a := hcoord.trans (by nlinarith)
  change |(1/(((n:ℚ)+1)*a))*v i|≤1
  rw [abs_mul,abs_of_pos (by positivity : (0:ℚ)<1/(((n:ℚ)+1)*a))]
  have he : (1/(((n:ℚ)+1)*a))*|v i|=|v i|/(((n:ℚ)+1)*a) := by ring
  rw [he]
  exact (div_le_one hd).mpr hm

def Bounded {n : ℕ} (s : State n) (M : ℚ) : Prop :=
  (∀ i, |s.center i|≤M) ∧ (∀ i j, |s.factor i j|≤M) ∧
    (∀ i j, |s.factor⁻¹ i j|≤M)

theorem bounded_mono {n : ℕ} (s : State n) {M N : ℚ} (h : Bounded s M) (hm : M≤N) :
    Bounded s N :=
  ⟨fun i => (h.1 i).trans hm,fun i j => (h.2.1 i j).trans hm,
    fun i j => (h.2.2 i j).trans hm⟩

theorem update_bounded {n : ℕ} (hn : 2≤n) (s : State n) (g : Vec n)
    (hR : s.factor.det≠0) (hg : g≠0) (M : ℚ) (hM : 0≤M) (hs : Bounded s M) :
    Bounded (update s g) (16*((n:ℚ)+1)*M) := by
  have hv := pulled_nonzero s g hR hg
  have hR' : ∀ i j, |(update s g).factor i j|≤(n:ℚ)*M*8 :=
    matrix_product s.factor (transform (pulled s g)) M 8 hM (by norm_num)
      hs.2.1 (transform_entry_bound hn _ hv)
  have hi : ∀ i j, |(update s g).factor⁻¹ i j|≤(n:ℚ)*4*M := by
    change ∀ i j, |(s.factor*transform (pulled s g))⁻¹ i j|≤_
    rw [Matrix.mul_inv_rev]
    exact matrix_product _ _ 4 M (by norm_num) hM
      (inverse_entry_bound hn _ hv) hs.2.2
  have hc : ∀ i, |(update s g).center i|≤M+(n:ℚ)*M := by
    intro i
    change |s.center i-(s.factor.mulVec (shift (pulled s g) • pulled s g)) i|≤_
    calc
      _ ≤ |s.center i|+|(s.factor.mulVec (shift (pulled s g) • pulled s g)) i| := abs_sub _ _
      _ ≤ M+(n:ℚ)*M := add_le_add (hs.1 i) (by
        calc
          _ ≤ ∑ j, |s.factor i j*(shift (pulled s g) • pulled s g) j| := by
            simpa only [Matrix.mulVec,dotProduct] using Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j : Fin n, M := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul]
            simpa only [mul_one] using mul_le_mul (hs.2.1 i j)
              (normalizer_coordinate hn _ hv j) (abs_nonneg _) hM
          _ = _ := by simp)
  exact ⟨fun i => (hc i).trans (by nlinarith [show (0:ℚ)≤n by positivity]),
    fun i j => (hR' i j).trans (by nlinarith [show (0:ℚ)≤n by positivity]),
    fun i j => (hi i j).trans (by nlinarith [show (0:ℚ)≤n by positivity])⟩

def growth (n k : ℕ) : ℕ := 2*(n+1)*(16*(n+1))^k
def exponent (n k : ℕ) : ℕ := (n+5)*(k+1)

theorem start_inverse (n : ℕ) :
    (start n).factor⁻¹=(1/(2*((n:ℚ)+1))) • (1 : Mat n) := by
  apply Matrix.inv_eq_right_inv
  change ((2*((n:ℚ)+1)) • (1 : Mat n))*((1/(2*((n:ℚ)+1))) • (1 : Mat n))=1
  rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul]
  rw [mul_one_div_cancel (by positivity : (2*((n:ℚ)+1))≠0),one_smul]

theorem start_bounded (n : ℕ) : Bounded (start n) (growth n 0) := by
  have hn0 : (0:ℚ)≤n := by positivity
  have hp : (0:ℚ)<2*((n:ℚ)+1) := by positivity
  have hh : (1:ℚ)/(2*((n:ℚ)+1))≤1 := (div_le_one hp).mpr (by nlinarith)
  have he : (growth n 0:ℚ)=2*((n:ℚ)+1) := by
    simp only [growth,pow_zero,mul_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  have hm : (1:ℚ)≤(growth n 0:ℚ) := by
    rw [he]
    linarith
  have hrec : (0:ℚ)<1/(2*((n:ℚ)+1)) := one_div_pos.mpr hp
  refine ⟨?_,?_,?_⟩
  · intro i
    change |(0:ℚ)|≤(growth n 0:ℚ)
    simpa only [abs_zero,he] using hp.le
  · intro i j
    simp only [start,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    split_ifs
    · simpa only [mul_one,abs_of_pos hp,he] using
        (le_rfl : 2*((n:ℚ)+1)≤2*((n:ℚ)+1))
    · simpa only [mul_zero,abs_zero,he] using hp.le
  · intro i j
    rw [start_inverse]
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    split_ifs
    · simpa only [mul_one,abs_of_pos hrec] using hh.trans hm
    · simpa only [mul_zero,abs_zero,he] using hp.le

theorem actual_bounded (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ) :
    Bounded (Trajectory.run d k) (growth d.dimension k) := by
  induction k with
  | zero => simpa only [Trajectory.run,Function.iterate_zero,Function.id_def] using start_bounded d.dimension
  | succ k ih =>
    have hM : (0:ℚ)≤(growth d.dimension k:ℕ) := by positivity
    have hm : (growth d.dimension k:ℚ)≤16*((d.dimension:ℚ)+1)*(growth d.dimension k:ℚ) := by
      nlinarith [show (0:ℚ)≤d.dimension by positivity]
    have he : (growth d.dimension (k+1):ℚ)=16*((d.dimension:ℚ)+1)*(growth d.dimension k:ℚ) := by
      simp only [growth,pow_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow]
      ring
    rw [show Trajectory.run d (k+1)=Trajectory.step d (Trajectory.run d k) from
      Function.iterate_succ_apply' _ _ _,he]
    cases hc : Separation.separate d (Trajectory.run d k).center with
    | none => simpa only [Trajectory.step,hc] using bounded_mono _ ih hm
    | some c =>
      by_cases hg : Separation.normal d c=0
      · simpa only [Trajectory.step,hc,if_pos hg] using bounded_mono _ ih hm
      · simp only [Trajectory.step,hc,if_neg hg]
        exact update_bounded hn _ _ (Trajectory.invariant d hn k).1 hg _ hM ih

theorem growth_power (n k : ℕ) : growth n k≤2^exponent n k := by
  have hn : n+1≤2^(n+1) := (Nat.lt_two_pow_self (n := n+1)).le
  have hb : 16*(n+1)≤2^(n+5) := by
    have h := Nat.mul_le_mul_left 16 hn
    simpa only [show n+5=(n+1)+4 by omega,pow_add,show 2^4=16 by norm_num,Nat.mul_comm] using h
  have hinit : 2*(n+1)≤2^(n+5) := (by nlinarith : 2*(n+1)≤16*(n+1)).trans hb
  have h := Nat.mul_le_mul hinit (Nat.pow_le_pow_left hb k)
  change 2*(n+1)*(16*(n+1))^k≤2^((n+5)*(k+1))
  calc
    _ ≤ 2^(n+5)*(2^(n+5))^k := h
    _ = (2^(n+5))^k*2^(n+5) := Nat.mul_comm _ _
    _ = (2^(n+5))^(k+1) := (pow_succ _ _).symm
    _ = 2^((n+5)*(k+1)) := (pow_mul _ _ _).symm

/-- Uniform over feasible AND infeasible original inputs and terminal rounds.
This still says nothing about reduced denominators before storage rounding. -/
theorem actual_power_bound (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ) :
    Bounded (Trajectory.run d k) (2^exponent d.dimension k:ℕ) :=
  bounded_mono _ (actual_bounded d hn k) (by exact_mod_cast growth_power d.dimension k)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RegisterGrowth
