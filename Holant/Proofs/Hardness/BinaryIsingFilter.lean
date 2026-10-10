import Holant.Proofs.Hardness.BinaryIsingWeights
import Holant.Proofs.Hardness.BinaryThreeSupportFilter
import Mathlib.Basic.Complex.Basic

/-! Exact linear-size annihilation of the unwanted Ising modes. All roots,
normalizations and divisions lie in the starting field. A positive real image
is used only to prove nonvanishing, never to implement an arithmetic operation.
The zeroth sample is supplied by its closed formula; all oracle exponents are
positive. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingFilter
open scoped BigOperators
namespace W
export BinaryIsingWeights (scalar scalar_ne_zero partition partition_zero normalized_partition
  moment internal_bound)
end W
namespace I
export EOBinaryPlaneIsing (internal Independent internal_zero independentCount)
end I
namespace D
export ThreeModeAnnihilator (differenceFilter differenceFilter_mul differenceFilter_sum)
end D
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K]

def roots (rho : K) (m : ℕ) : List K := (List.range m).map (fun j=>rho^(2*(j+1)))

@[simp] theorem roots_length (rho : K) (m : ℕ) : (roots rho m).length=m := by simp [roots]

theorem power_mem_roots (rho : K) {m j : ℕ} (hj : 0<j) (hm : j≤m) :
    rho^(2*j)∈roots rho m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  exact List.mem_map.mpr ⟨k,List.mem_range.mpr (by omega),rfl⟩

def denominator (rho : K) (m : ℕ) : K := ((roots rho m).map (fun r=>1-r)).prod

theorem denominator_ne_zero (rho : K) (m : ℕ)
    (h : ∀j,0<j → rho^(2*j)≠1) : denominator rho m≠0 := by
  apply List.prod_ne_zero
  intro ha
  obtain ⟨r,hr,he⟩ := List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hr
  exact (sub_ne_zero.mpr (h (j+1) (by omega)).symm) he

/-- A real positive nonunit image rules out every undesired mode being one.
The embedding may have complex codomain, as the original coefficient field
need not itself be an ordered field. -/
theorem positive_image_ne_one (rho : K) (ι : K→+*ℂ) (r : ℝ)
    (hr : 0<r) (hne : r≠1) (hi : ι rho=(r : ℂ)) (j : ℕ) (hj : 0<j) :
    rho^(2*j)≠1 := by
  intro h
  have hh := congrArg ι h
  rw [map_pow,map_one,hi] at hh
  have hrpow : r^(2*j)=1 := by
    apply Complex.ofReal_injective
    simpa using hh
  exact hne ((pow_eq_one_iff_of_nonneg hr.le (by omega)).mp hrpow)

theorem filter_statistic {V : Type*} [Fintype V] (stat : V→ℕ) (rho : K) (m : ℕ)
    (hs : ∀x,stat x≤m) :
    D.differenceFilter (roots rho m) (fun j=>∑x,(rho^(2*stat x))^j) 0=
      (∑x,if stat x=0 then (1 : K) else 0)*denominator rho m := by
  classical
  rw [D.differenceFilter_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [BinaryThreeSupportFilter.filter_moment]
  simp only [pow_zero,one_mul]
  by_cases hx : stat x=0
  · simp [hx,denominator]
  · rw [ite_eq_right hx,zero_mul]
    apply List.prod_eq_zero_iff.mpr
    exact List.mem_map.mpr ⟨rho^(2*stat x),power_mem_roots rho (by omega) (hs x),sub_self _⟩

theorem filter_moment {m n : ℕ} (rho : K) (left right : Fin m→Fin n) :
    D.differenceFilter (roots rho m) (W.moment rho left right) 0=
      (I.independentCount left right : K)*denominator rho m := by
  unfold W.moment
  rw [filter_statistic (I.internal left right) rho m (W.internal_bound left right)]
  congr 1
  simp only [I.independentCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : I.internal left right x=0
  · have hi := (I.internal_zero left right x).mp hx
    simp [hx,hi]
  · have hi : ¬I.Independent left right x := fun h=>hx ((I.internal_zero left right x).mpr h)
    simp [hx,hi]

/-- Only the positive indices require a partition-function query. -/
def samples {m n : ℕ} (p q : K) (left right : Fin m→Fin n) (k : ℕ) : K :=
  if k=0 then (2 : K)^(n+1) else W.partition p q left right k/W.scalar p q m^k

theorem samples_eq {m n : ℕ} (p q : K) (hp : p≠0) (hq : q≠0)
    (left right : Fin m→Fin n) (k : ℕ) :
    samples p q left right k=2*W.moment (q/p) left right k := by
  unfold samples
  split_ifs with hk
  · subst k
    rw [←W.partition_zero p q left right]
    simpa using W.normalized_partition p q hp hq left right 0
  · exact W.normalized_partition p q hp hq left right k

/-- Exactly m positive queries suffice. The zero-edge graph uses no query and
keeps all 2^n assignments; there is one global apex factor 2. -/
theorem extract [CharZero K] {m n : ℕ} (p q : K) (hp : p≠0) (hq : q≠0)
    (left right : Fin m→Fin n) (hr : ∀j,0<j→(q/p)^(2*j)≠1) :
    (I.independentCount left right : K)=
      D.differenceFilter (roots (q/p) m) (samples p q left right) 0 /
        (2*denominator (q/p) m) := by
  have he : samples p q left right=(fun k=>2*W.moment (q/p) left right k) := by
    funext k
    exact samples_eq p q hp hq left right k
  rw [he,D.differenceFilter_mul,filter_moment]
  have hden := denominator_ne_zero (q/p) m hr
  have htwo : (2 : K)≠0 := by norm_num
  field_simp

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingFilter
