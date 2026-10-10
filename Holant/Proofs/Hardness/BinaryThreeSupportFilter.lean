import Holant.Proofs.Hardness.BinaryThreeSupportAnnihilator
import Holant.Proofs.Hardness.ThreeModeAnnihilatorDifference

/-! Support extraction by the already implemented adjacent-difference
programme, at desired root zero. The zeroth moment is the declared assignment
count, so only the positive moments are oracle queries. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportFilter
open scoped BigOperators
namespace D
export ThreeModeAnnihilator (differenceFilter differenceFilter_mul differenceFilter_sum)
end D
namespace A
export BinaryThreeSupportAnnihilator (Grid monomial monomial_ne_zero product_spectrum)
end A
variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem filter_moment (roots : List K) (t : K) (k : ℕ) :
    D.differenceFilter roots (fun j=>t^j) k=
      t^k*(roots.map (fun r=>t-r)).prod := by
  induction roots with
  | nil => simp
  | cons r rs ih =>
    rw [ThreeModeAnnihilator.differenceFilter_cons]
    have he : (fun j=>t^(j+1)-r*t^j)=(fun j=>(t-r)*t^j) := by
      funext j
      rw [pow_succ]
      ring
    rw [he,D.differenceFilter_mul,ih]
    simp only [List.map_cons,List.prod_cons]
    ring

def denominator (roots : List K) : K := (roots.map (fun r=> -r)).prod

theorem denominator_ne_zero (roots : List K) (hr : ∀r∈roots,r≠0) : denominator roots≠0 := by
  induction roots with
  | nil => simp [denominator]
  | cons r rs ih =>
    have hh : r≠0 := hr r (by simp)
    have ht : denominator rs≠0 := ih (fun x hx=>hr x (by simp [hx]))
    exact mul_ne_zero (neg_ne_zero.mpr hh) ht

theorem filter_count_zero {V : Type*} [Fintype V] (w : V→K) (roots : List K)
    (hs : ∀x,w x≠0→w x∈roots) :
    D.differenceFilter roots (fun j=>∑x,w x^j) 0=
      (∑x,if w x=0 then (1 : K) else 0)*denominator roots := by
  rw [D.differenceFilter_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [filter_moment]
  simp only [pow_zero,one_mul]
  by_cases hx : w x=0
  · simp [hx,denominator]
  · rw [ite_eq_right hx,zero_mul]
    apply List.prod_eq_zero_iff.mpr
    exact List.mem_map.mpr ⟨w x,hs x hx,sub_self _⟩

/-- This is the exact final subtraction after the existing finite filter's
division. No zeroth-power target query is needed. -/
theorem count_nonzero {V : Type*} [Fintype V] (w : V→K) (roots : List K)
    (hr : ∀r∈roots,r≠0) (hs : ∀x,w x≠0→w x∈roots) :
    (∑x,if w x=0 then (0 : K) else 1)=
      (Fintype.card V : K)-D.differenceFilter roots (fun j=>∑x,w x^j) 0/denominator roots := by
  rw [filter_count_zero w roots hs,mul_div_cancel_right₀ _ (denominator_ne_zero roots hr)]
  have h : (∑x,if w x=0 then (0 : K) else 1)+
      (∑x,if w x=0 then (1 : K) else 0)=(Fintype.card V : K) := by
    rw [←Finset.sum_add_distrib]
    have he (x : V) : (if w x=0 then (0 : K) else 1)+(if w x=0 then 1 else 0)=1 := by
      split_ifs <;> simp
    simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact eq_sub_of_add_eq h

def cubeRoots (n : ℕ) (a b c : K) : List K :=
  (List.range (n+1)).flatMap (fun i=>(List.range (n+1)).flatMap
    (fun j=>(List.range (n+1)).map (fun k=>a^i*b^j*c^k)))

theorem cubeRoots_length (n : ℕ) (a b c : K) :
    (cubeRoots n a b c).length=(n+1)^3 := by
  simp [cubeRoots,List.length_flatMap,List.sum_replicate,pow_succ,Nat.mul_assoc]

theorem monomial_mem (n : ℕ) (a b c : K) (i : A.Grid n) :
    A.monomial a b c i∈cubeRoots n a b c := by
  apply List.mem_flatMap.mpr
  refine ⟨i.1.val,List.mem_range.mpr i.1.isLt,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨i.2.1.val,List.mem_range.mpr i.2.1.isLt,?_⟩
  exact List.mem_map.mpr ⟨i.2.2.val,List.mem_range.mpr i.2.2.isLt,rfl⟩

theorem cubeRoots_nonzero (n : ℕ) {a b c : K} (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    ∀r∈cubeRoots n a b c,r≠0 := by
  intro r hr
  obtain ⟨i,hi,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨j,hj,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)) (pow_ne_zero _ hc)

theorem count_constraints {V : Type*} [Fintype V] {n : ℕ}
    (f : V→Fin n→K) {a b c : K} (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hf : ∀x i,f x i=0 ∨ f x i=a ∨ f x i=b ∨ f x i=c) :
    (∑x,if (∏i,f x i)=0 then (0 : K) else 1)=
      (Fintype.card V : K)-D.differenceFilter (cubeRoots n a b c)
        (fun j=>∑x,∏i,f x i^j) 0/denominator (cubeRoots n a b c) := by
  have hs (x : V) (hx : (∏i,f x i)≠0) : (∏i,f x i)∈cubeRoots n a b c := by
    obtain ⟨i,hi⟩ := A.product_spectrum (f x) a b c (hf x) hx
    rw [hi]
    exact monomial_mem n a b c i
  simpa only [Finset.prod_pow] using
    count_nonzero (fun x=>∏i,f x i) (cubeRoots n a b c) (cubeRoots_nonzero n ha hb hc) hs

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportFilter
