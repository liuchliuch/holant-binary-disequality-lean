import Holant.ReedMuller.DiagonalSlice.Basic
import Mathlib.Data.Finset.Card

/-! Direct integration in four or more coordinates. A disjoint equal-coordinate
slice determines every two-coordinate coefficient; any remaining word lies in
an equal-coordinate slice. -/
namespace Holant.ReedMuller.DiagonalSlice
open scoped BigOperators
variable {α G : Type*} [Fintype α] [DecidableEq α] [CommGroup G]

theorem card_outside (i j : α) (hij : i ≠ j) :
    (outside i j).card = Fintype.card α - 2 := by
  simp [outside,Finset.card_erase_of_mem,Ne.symm hij]
  omega

theorem pair_product {h : Finset α → G} (h0 : h ∅ = 1)
    (hn : 4 ≤ Fintype.card α) (hs : ∀ i j, i ≠ j → Simple h i j)
    (i j : α) (hij : i ≠ j) : h {i,j} = h {i} * h {j} := by
  have hc : 1 < (outside i j).card := by rw [card_outside i j hij]; omega
  obtain ⟨k,hk,l,hl,hkl⟩ := Finset.one_lt_card.mp hc
  obtain ⟨hki,hkj⟩ := (mem_outside i j k).mp hk
  obtain ⟨hli,hlj⟩ := (mem_outside i j l).mp hl
  have H := slice_formula h0 hkl (hs k l hkl) {i,j} (by simp [hki,hkj,hli,hlj])
  have he : outside k l ∩ {i,j} = {i,j} := by
    ext a
    simp
    aesop
  simpa [hki,hkj,he,hij] using H

theorem prod_pair_complement (f : α → G) (S : Finset α) (i j : α)
    (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) :
    (f i * f j) * (∏ k ∈ outside i j ∩ S, f k) = ∏ k ∈ S, f k := by
  have he : outside i j ∩ S = (S.erase i).erase j := by ext k; simp; tauto
  rw [he]
  have hje : j ∈ S.erase i := by simp [Ne.symm hij,hj]
  rw [←Finset.mul_prod_erase _ _ hi,←Finset.mul_prod_erase _ _ hje]
  exact mul_assoc _ _ _

theorem equal_pair_exists (S : Finset α) (hn : 3 ≤ Fintype.card α) :
    ∃ i j : α, i ≠ j ∧ (i ∈ S ↔ j ∈ S) := by
  by_cases hc : 1 < S.card
  · obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hc
    exact ⟨i,j,hij,by simp [hi,hj]⟩
  · have hc' : 1 < (Finset.univ \ S).card := by
      rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ]
      omega
    obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hc'
    exact ⟨i,j,hij,by simp_all⟩

/-- Every coefficient is the product of the actual singleton coefficients. -/
theorem integrate {h : Finset α → G} (h0 : h ∅ = 1)
    (hn : 4 ≤ Fintype.card α) (hs : ∀ i j, i ≠ j → Simple h i j)
    (S : Finset α) : h S = ∏ i ∈ S, h {i} := by
  obtain ⟨i,j,hij,hS⟩ := equal_pair_exists S (by omega)
  rw [slice_formula h0 hij (hs i j hij) S hS]
  by_cases hi : i ∈ S
  · rw [if_pos hi,pair_product h0 hn hs i j hij]
    exact prod_pair_complement (fun k => h {k}) S i j hij hi (hS.mp hi)
  · have hj : j ∉ S := by simpa [hi] using hS
    rw [if_neg hi,one_mul]
    have he : outside i j ∩ S = S := by ext k; simp; aesop
    rw [he]

end Holant.ReedMuller.DiagonalSlice
