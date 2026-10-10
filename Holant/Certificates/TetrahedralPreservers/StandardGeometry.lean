import Holant.Certificates.TetrahedralPreservers.InvertibleAction

/-! Elementary support geometry of the actual twelve standard quaternion
coefficient points, used to constrain arbitrary invertible preservers. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open Holant.Certificates.RainbowOrbit
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

def standardTable : Fin 12 → V :=
  ![![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1],
    ![1,1,1,1],![1,1,1,-1],![1,1,-1,1],![1,1,-1,-1],
    ![1,-1,1,1],![1,-1,1,-1],![1,-1,-1,1],![1,-1,-1,-1]]

theorem standardPoint_table (k : Fin 12) : standardPoint k=standardTable k := by
  ext i
  change coordinates (goldenMatrix (raw .tetrahedral k)) i = standardTable k i
  rw [coordinates_golden]
  fin_cases k <;> fin_cases i <;>
    norm_num [raw,tetrahedralRaw,GoldenInt.eval,standardTable]

def axisIndex (i : Fin 4) : Fin 12 := ⟨i.val,by omega⟩

theorem standardPoint_axis (i : Fin 4) : standardPoint (axisIndex i) = Pi.single i 1 := by
  rw [standardPoint_table]
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [axisIndex,standardTable,Pi.single_apply]

theorem standardPoint_support (k : Fin 12) :
    (∃ i : Fin 4, standardPoint k = Pi.single i 1) ∨ ∀ i : Fin 4, standardPoint k i ≠ 0 := by
  rw [standardPoint_table]
  fin_cases k
  · exact Or.inl ⟨0,by ext i; fin_cases i <;> norm_num [standardTable,Pi.single_apply]⟩
  · exact Or.inl ⟨1,by ext i; fin_cases i <;> norm_num [standardTable,Pi.single_apply]⟩
  · exact Or.inl ⟨2,by ext i; fin_cases i <;> norm_num [standardTable,Pi.single_apply]⟩
  · exact Or.inl ⟨3,by ext i; fin_cases i <;> norm_num [standardTable,Pi.single_apply]⟩
  all_goals right; intro i; fin_cases i <;> norm_num [standardTable]

theorem standard_two_nonzero {r : V} (hr : r ∈ Standard) {i j : Fin 4}
    (hij : i ≠ j) (hi : r i ≠ 0) (hj : r j ≠ 0) : ∀ k : Fin 4, r k ≠ 0 := by
  obtain ⟨p,c,hc,rfl⟩ := (standard_iff r).mp hr
  rcases standardPoint_support p with ⟨a,ha⟩ | ha
  · rw [ha] at hi hj
    have hai : i=a := by by_contra h; simp [Pi.single_apply,h,Ne.symm h] at hi
    have haj : j=a := by by_contra h; simp [Pi.single_apply,h,Ne.symm h] at hj
    exact False.elim (hij (hai.trans haj.symm))
  · intro k
    exact mul_ne_zero hc (ha k)

theorem no_two_support (i : Fin 3) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a • Pi.single (0 : Fin 4) 1 + b • Pi.single i.succ 1 ∉ Standard := by
  intro h
  have h0 : (a • Pi.single (0 : Fin 4) (1 : ℂ) + b • Pi.single i.succ 1 : V) 0 ≠ 0 := by
    simpa [Pi.single_apply,Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero i)] using ha
  have hi : (a • Pi.single (0 : Fin 4) (1 : ℂ) + b • Pi.single i.succ 1 : V) i.succ ≠ 0 := by
    simpa [Pi.single_apply,Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero i)] using hb
  have hall := standard_two_nonzero h (Ne.symm (Fin.succ_ne_zero i)) h0 hi
  fin_cases i
  · simpa [Pi.single_apply] using hall 2
  · simpa [Pi.single_apply] using hall 1
  · simpa [Pi.single_apply] using hall 1

def complementIndex : Fin 12 → Fin 12 := ![0,1,2,3,11,10,9,8,7,6,5,4]

theorem standard_complement (k : Fin 12) (hk : 4 ≤ k.val) :
    standardPoint (complementIndex k) = (2 : ℂ) • Pi.single (0 : Fin 4) 1 - standardPoint k := by
  simp only [standardPoint_table]
  fin_cases k <;> norm_num at hk
  all_goals ext i; fin_cases i <;> norm_num [complementIndex,standardTable,Pi.single_apply]

theorem standard_axis_or_full (k : Fin 12) :
    (∃ i : Fin 4, k=axisIndex i) ∨ 4 ≤ k.val := by
  by_cases h : k.val < 4
  · exact Or.inl ⟨⟨k.val,h⟩,rfl⟩
  · exact Or.inr (by omega)

theorem standard_full_zero (k : Fin 12) (hk : 4 ≤ k.val) : standardPoint k 0=1 := by
  rw [standardPoint_table]
  fin_cases k <;> norm_num at hk <;> norm_num [standardTable]

theorem standard_full_sign (k : Fin 12) (hk : 4 ≤ k.val) (i : Fin 4) :
    standardPoint k i=1 ∨ standardPoint k i= -1 := by
  rw [standardPoint_table]
  fin_cases k <;> norm_num at hk
  all_goals fin_cases i <;> norm_num [standardTable]

theorem standard_coordinate_signs {r : V} (hr : r ∈ Standard) (h0 : r 0=1)
    (hother : ∃ j : Fin 4, j ≠ 0 ∧ r j ≠ 0) (i : Fin 4) : r i=1 ∨ r i= -1 := by
  obtain ⟨k,c,hc,rfl⟩ := (standard_iff r).mp hr
  rcases standard_axis_or_full k with ⟨j,rfl⟩ | hk
  · rw [standardPoint_axis] at h0 hother ⊢
    have hj : j=0 := by
      by_contra hj
      simp [Pi.single_apply,hj,Ne.symm hj] at h0
    subst j
    obtain ⟨j,hj,hv⟩ := hother
    simp [Pi.single_apply,hj,Ne.symm hj] at hv
  · have hc1 : c=1 := by simpa [standard_full_zero k hk] using h0
    simpa only [hc1,one_smul] using standard_full_sign k hk i

end Holant.Certificates.TetrahedralPreservers
