import Holant.Proofs.Hardness.BinaryIsingFilter

/-! The actual adjacent-difference interpreter can consume raw partition
answers: multiply every root and the desired mode by the common scalar. This
avoids dividing individual oracle answers before filtering. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingUnnormalized
open scoped BigOperators
namespace W
export BinaryIsingWeights (scalar scalar_ne_zero partition partition_eq moment internal_bound)
end W
namespace I
export EOBinaryPlaneIsing (internal independentCount internal_zero)
end I
namespace A
export BinaryIsingFilter (roots power_mem_roots denominator denominator_ne_zero)
end A
namespace D
export ThreeModeAnnihilator (differenceFilter differenceFilter_sum differenceFilter_mul)
end D
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

def roots (c rho : K) (m : ℕ) : List K := (A.roots rho m).map (fun r=>c*r)
def denominator (c rho : K) (m : ℕ) : K := ((roots c rho m).map (fun r=>c-r)).prod

@[simp] theorem roots_length (c rho : K) (m : ℕ) : (roots c rho m).length=m := by simp [roots]

theorem denominator_ne_zero (c rho : K) (hc : c≠0) (m : ℕ)
    (hr : ∀j,0<j → rho^(2*j)≠1) : denominator c rho m≠0 := by
  apply List.prod_ne_zero
  intro hz
  obtain ⟨r,hrm,he⟩ := List.mem_map.mp hz
  obtain ⟨v,hv,hve⟩ := List.mem_map.mp hrm
  obtain ⟨j,_,hje⟩ := List.mem_map.mp hv
  rw [←hve,←hje] at he
  have hh : c*(1-rho^(2*(j+1)))≠0 :=
    mul_ne_zero hc (sub_ne_zero.mpr (hr (j+1) (by omega)).symm)
  apply hh
  linear_combination he

theorem filter_statistic {V : Type*} [Fintype V] (stat : V→ℕ) (c rho : K) (m : ℕ)
    (hs : ∀x,stat x≤m) :
    D.differenceFilter (roots c rho m) (fun j=>∑x,(c*rho^(2*stat x))^j) 0=
      (∑x,if stat x=0 then (1 : K) else 0)*denominator c rho m := by
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
    refine List.mem_map.mpr ⟨c*rho^(2*stat x),?_,sub_self _⟩
    exact List.mem_map.mpr ⟨rho^(2*stat x),A.power_mem_roots rho (by omega) (hs x),rfl⟩

theorem partition_moment {m n : ℕ} (p q : K) (hp : p≠0)
    (left right : Fin m→Fin n) (k : ℕ) :
    W.partition p q left right k=
      2*∑x : Fin n→Bool,(W.scalar p q m*(q/p)^(2*I.internal left right x))^k := by
  rw [W.partition_eq p q hp]
  simp_rw [mul_pow]
  rw [←Finset.mul_sum]
  unfold W.moment
  ring

theorem filter_partition {m n : ℕ} (p q : K) (hp : p≠0)
    (left right : Fin m→Fin n) :
    D.differenceFilter (roots (W.scalar p q m) (q/p) m) (W.partition p q left right) 0=
      2*(I.independentCount left right : K)*denominator (W.scalar p q m) (q/p) m := by
  have he : W.partition p q left right=(fun k=>
      2*∑x : Fin n→Bool,(W.scalar p q m*(q/p)^(2*I.internal left right x))^k) := by
    funext k
    exact partition_moment p q hp left right k
  rw [he,D.differenceFilter_mul,filter_statistic _ _ _ m (W.internal_bound left right)]
  have hc : (∑x : Fin n→Bool,if I.internal left right x=0 then (1 : K) else 0)=
      (I.independentCount left right : K) := by
    simp only [I.independentCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : I.internal left right x=0
    · have hi := (I.internal_zero left right x).mp hx
      simp [hx,hi]
    · have hi : ¬EOBinaryPlaneIsing.Independent left right x := fun h=>hx ((I.internal_zero left right x).mpr h)
      simp [hx,hi]
  rw [hc]
  ring

theorem extract [CharZero K] {m n : ℕ} (p q : K) (hp : p≠0) (hq : q≠0)
    (left right : Fin m→Fin n) (hr : ∀j,0<j → (q/p)^(2*j)≠1) :
    (I.independentCount left right : K)=
      (D.differenceFilter (roots (W.scalar p q m) (q/p) m) (W.partition p q left right) 0 /
        denominator (W.scalar p q m) (q/p) m)/2 := by
  rw [filter_partition p q hp,mul_div_cancel_right₀ _
    (denominator_ne_zero _ _ (W.scalar_ne_zero hp hq m) m hr)]
  symm
  exact mul_div_cancel_left₀ _ (by norm_num)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingUnnormalized
