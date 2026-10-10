import Holant.Proofs.LinearProgramming.Optimization.Search.RoundedGeometry
import Mathlib.Data.Int.AbsoluteValue

/-!
A determinant perturbation bound for the actual entrywise storage rounding.
Leibniz products are bounded by an elementary finite induction. The large
factor n! n 2^n is paid with binary precision, never enumeration of matrices
or permutations by the algorithm. This supplies the rounding part of local
progress; RoundedTrajectory discharges its grid bounds in the whole-search invariant.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RoundingDeterminant
open FactorUpdate Containment RoundedGeometry
open scoped BigOperators Matrix
noncomputable section

theorem product_bound {I : Type} [DecidableEq I] (s : Finset I) (f : I→ℚ)
    (hf : ∀ i∈s, |f i|≤2) : |∏ i∈s, f i|≤2^s.card := by
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf; simp
  | @insert a s ha ih =>
    intro hf
    rw [Finset.prod_insert ha,abs_mul,Finset.card_insert_of_notMem ha,pow_succ]
    have h := mul_le_mul (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))) (abs_nonneg _) (by norm_num : (0:ℚ)≤2)
    simpa only [mul_comm] using h

theorem product_difference {I : Type} [DecidableEq I] (s : Finset I) (f g : I→ℚ)
    (delta : ℚ) (hd : 0≤delta) (hf : ∀ i∈s, |f i|≤2) (hg : ∀ i∈s, |g i|≤2)
    (he : ∀ i∈s, |f i-g i|≤delta) :
    |(∏ i∈s, f i)-(∏ i∈s, g i)|≤(s.card:ℚ)*delta*2^s.card := by
  revert hf hg he
  induction s using Finset.induction_on with
  | empty => intro hf hg he; simp
  | @insert a s ha ih =>
    intro hf hg he
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have he' := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hp := ih hf' hg' he'
    have hprod := product_bound s g hg'
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hea := he a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.card_insert_of_notMem ha]
    have hid : f a*(∏ i∈s, f i)-g a*(∏ i∈s, g i)=
        f a*((∏ i∈s, f i)-(∏ i∈s, g i))+(f a-g a)*(∏ i∈s, g i) := by ring
    rw [hid]
    calc
      _ ≤ |f a*((∏ i∈s, f i)-(∏ i∈s, g i))|+|(f a-g a)*(∏ i∈s, g i)| := abs_add_le _ _
      _ ≤ 2*((s.card:ℚ)*delta*2^s.card)+delta*2^s.card := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul hfa hp (abs_nonneg _) (by norm_num))
          (mul_le_mul hea hprod (abs_nonneg _) hd)
      _ ≤ ((s.card+1:ℕ):ℚ)*delta*2^(s.card+1) := by
        push_cast
        rw [pow_succ]
        nlinarith [show (0:ℚ)≤delta*2^s.card by positivity]

def coefficient (n : ℕ) : ℕ := n.factorial*n*2^n

theorem near_identity {n : ℕ} (E : Mat n) (delta : ℚ) (hd : 0≤delta) (hd1 : delta≤1)
    (he : ∀ i j, |E i j|≤delta) : |(1+E).det-1|≤(coefficient n:ℚ)*delta := by
  have hI : ∀ i j, |(1 : Mat n) i j|≤1 := by
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hA : ∀ i j, |(1+E) i j|≤2 := by
    intro i j
    change |(1 : Mat n) i j+E i j|≤2
    exact (abs_add_le _ _).trans (by linarith [hI i j,he i j])
  have hprod : ∀ p : Equiv.Perm (Fin n),
      |(∏ i, (1+E) (p i) i)-(∏ i, (1 : Mat n) (p i) i)|≤(n:ℚ)*delta*2^n := by
    intro p
    simpa only [Finset.card_univ,Fintype.card_fin] using
      product_difference Finset.univ (fun i => (1+E) (p i) i)
        (fun i => (1 : Mat n) (p i) i) delta hd
        (fun i _ => hA _ _) (fun i _ => (hI _ _).trans (by norm_num))
        (fun i _ => by
          change |((1 : Mat n) (p i) i+E (p i) i)-(1 : Mat n) (p i) i|≤_
          simpa only [add_sub_cancel_left] using he (p i) i)
  have hdet : |(1+E).det-(1 : Mat n).det|≤(coefficient n:ℚ)*delta := by
    rw [Matrix.det_apply,Matrix.det_apply,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ p : Equiv.Perm (Fin n),
          |Equiv.Perm.sign p • (∏ i, (1+E) (p i) i)-Equiv.Perm.sign p • (∏ i, (1 : Mat n) (p i) i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p : Equiv.Perm (Fin n),
          |(∏ i, (1+E) (p i) i)-(∏ i, (1 : Mat n) (p i) i)| := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← smul_sub]
        exact AbsoluteValue.abs.map_units_int_smul _ _
      _ ≤ ∑ _p : Equiv.Perm (Fin n), (n:ℚ)*delta*2^n :=
        Finset.sum_le_sum (fun p _ => hprod p)
      _ = _ := by simp [coefficient,Fintype.card_perm]; ring
  simpa only [Matrix.det_one] using hdet

theorem determinant_factor {n : ℕ} (A B : Mat n) (hA : A.det≠0) :
    B.det=A.det*(1+relative A B).det := by
  have hm : A*(1+relative A B)=B := by
    have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    rw [relative,Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu,Matrix.one_mul]
    abel
  calc
    B.det=(A*(1+relative A B)).det := congrArg Matrix.det hm.symm
    _ = _ := Matrix.det_mul _ _

theorem relative_det_bound {n : ℕ} (A B : Mat n) (hA : A.det≠0)
    (delta : ℚ) (hd : 0≤delta) (hd1 : delta≤1)
    (hr : ∀ i j, |relative A B i j|≤delta) :
    |B.det|≤|A.det| *(1+(coefficient n:ℚ)*delta) := by
  have h := near_identity (relative A B) delta hd hd1 hr
  have hb : |(1+relative A B).det|≤1+(coefficient n:ℚ)*delta := by
    calc
      _ ≤ |(1+relative A B).det-1|+|1| := by
        simpa only [sub_add_cancel] using abs_add_le ((1+relative A B).det-1) 1
      _ ≤ 1+(coefficient n:ℚ)*delta := by norm_num at *; linarith
  rw [determinant_factor A B hA,abs_mul]
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

def loss (n : ℕ) : ℚ := 1/(2*((n:ℚ)^3+1))
def eta (n : ℕ) : ℚ := 1/(64*(n:ℚ)*((n:ℚ)^3+1))
def contraction (n : ℕ) : ℚ := 1-loss n/2

theorem loss_pos (n : ℕ) : 0<loss n := by unfold loss; positivity
theorem loss_le_one (n : ℕ) : loss n≤1 := by
  unfold loss
  apply (div_le_one (by positivity)).mpr
  have : (0:ℚ)≤(n:ℚ)^3 := by positivity
  linarith
theorem eta_pos (n : ℕ) (hn : 0<n) : 0<eta n := by unfold eta; positivity
theorem contraction_pos (n : ℕ) : 0<contraction n := by
  unfold contraction
  have := loss_le_one n
  linarith
theorem contraction_lt_one (n : ℕ) : contraction n<1 := by
  unfold contraction
  have := loss_pos n
  linarith

theorem inflation_bound (n : ℕ) (hn : 0<n) : (1+eta n)^n≤1+loss n/8 := by
  have hr := loss_pos n
  have hr1 := loss_le_one n
  have he := eta_pos n hn
  have hid : (n:ℚ)*eta n=loss n/32 := by
    unfold eta loss
    have hN : (n:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
    <;> ring
  have hsmall : (n:ℚ)*eta n<1 := by rw [hid]; linarith
  have hp := Scales.pow_upper (eta n) he.le n hsmall
  rw [hid] at hp
  have hb : 1/(1-loss n/32)≤1+loss n/8 := by
    apply (div_le_iff₀ (by linarith : (0:ℚ)<1-loss n/32)).mpr
    nlinarith [mul_nonneg hr.le (by linarith : (0:ℚ)≤1-loss n)]
  exact hp.trans hb

theorem rounded_det {n : ℕ} (hn : 0<n) (s : State n) (h : ℕ) (hh : 0<h)
    (hR : s.factor.det≠0) (M : ℚ) (hM : 0≤M) (hi : ∀ i j, |s.factor⁻¹ i j|≤M)
    (hd1 : (n:ℚ)*M/(h:ℚ)≤1)
    (hdet : (coefficient n:ℚ)*((n:ℚ)*M/(h:ℚ))≤loss n/8) :
    |(RoundedGeometry.value s h (eta n)).factor.det|≤|s.factor.det| *(1+loss n/8)^2 := by
  let delta : ℚ := (n:ℚ)*M/(h:ℚ)
  have hd : 0≤delta := by dsimp [delta]; positivity
  have hr : ∀ i j, |relative s.factor (roundedMatrix s.factor h) i j|≤delta := by
    intro i j
    simpa only [delta,mul_one_div] using relative_entry_bound s.factor (roundedMatrix s.factor h)
      M (1/(h:ℚ)) hM (by positivity) hi (round_error s h hh).2 i j
  have hb := relative_det_bound s.factor (roundedMatrix s.factor h) hR delta hd hd1 hr
  have hfactor : |(roundedMatrix s.factor h).det|≤|s.factor.det| *(1+loss n/8) :=
    hb.trans (mul_le_mul_of_nonneg_left (by linarith [hdet]) (abs_nonneg _))
  change |((1+eta n) • roundedMatrix s.factor h).det|≤_
  rw [Matrix.det_smul,Fintype.card_fin,abs_mul,abs_of_pos (pow_pos (by have := eta_pos n hn; linarith) n)]
  calc
    _ ≤ (1+loss n/8)*(|s.factor.det| *(1+loss n/8)) :=
      mul_le_mul (inflation_bound n hn) hfactor (abs_nonneg _) (by have := loss_pos n; positivity)
    _ = _ := by ring

theorem total_contraction (n : ℕ) :
    Scales.contraction n*(1+loss n/8)^2≤contraction n := by
  have hr := loss_pos n
  have hr1 := loss_le_one n
  change (1-loss n)*(1+loss n/8)^2≤1-loss n/2
  have h1 : (1+loss n/8)^2≤1+loss n/2 := by nlinarith
  calc
    _ ≤ (1-loss n)*(1+loss n/2) := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ _ := by nlinarith

theorem coefficient_power (n : ℕ) : coefficient n≤2^(n*n+2*n) := by
  have hf := DeterminantGap.bound_le_power n 1 0 (by norm_num : 1≤2^0)
  have hf' : n.factorial≤2^(n*n) := by simpa [DeterminantGap.bound] using hf
  have hn : n≤2^n := (Nat.lt_two_pow_self (n := n)).le
  have h := Nat.mul_le_mul (Nat.mul_le_mul hf' hn) (le_refl (2^n))
  simpa [coefficient,pow_add,Nat.mul_assoc,Nat.two_mul] using h

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.RoundingDeterminant
