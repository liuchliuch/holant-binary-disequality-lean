import Holant.Pauli.ExoticKlein.Basic

/-! The two literal cross orientations cannot both have constant fused labels.
Only surjectivity of the first label map is used; no affine classification of
permutations or supplied nonconstant orientation is assumed. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticOrientation
open Holant.Pauli.ExoticKlein

/-- The actual labels at preimages of zero and y already witness one orientation. -/
theorem at_zero_y {I : Type*} (A B : I → Label) (i j : I)
    (hi : A i = 0) (hj : A j = yLabel) :
    A i + B i ≠ A j + B j ∨ theta (A i) + B i ≠ theta (A j) + B j := by
  by_cases h : A i + B i = A j + B j
  · right
    intro ht
    have hn : B i = yLabel + B j := by simpa only [hi,hj,zero_add] using h
    have hr : B i = zLabel + B j := by
      simpa only [hi,hj,theta_zero,theta_y,zero_add] using ht
    exact y_ne_z (add_right_cancel (hn.symm.trans hr))
  · exact Or.inl h

/-- Some pair of actual source labels distinguishes one of the two orientations. -/
theorem one_orientation_nonconstant {I : Type*} (A B : I → Label)
    (surjective : Function.Surjective A) :
    (∃ i j, A i + B i ≠ A j + B j) ∨
      (∃ i j, theta (A i) + B i ≠ theta (A j) + B j) := by
  obtain ⟨i,hi⟩ := surjective 0
  obtain ⟨j,hj⟩ := surjective yLabel
  rcases at_zero_y A B i j hi hj with h | h
  · exact Or.inl ⟨i,j,h⟩
  · exact Or.inr ⟨i,j,h⟩

def fused {I : Type*} (A B : I → Label) (reverse : Bool) (i : I) : Label :=
  (if reverse then theta (A i) else A i) + B i

/-- A reversal choice with explicit distinct actual inputs; no new label is chosen. -/
theorem exists_orientation {I : Type*} (A B : I → Label)
    (surjective : Function.Surjective A) :
    ∃ reverse : Bool, ∃ i j, fused A B reverse i ≠ fused A B reverse j := by
  rcases one_orientation_nonconstant A B surjective with ⟨i,j,h⟩ | ⟨i,j,h⟩
  · exact ⟨false,i,j,h⟩
  · exact ⟨true,i,j,h⟩

/-- Adding the same kernel label cannot erase the witnessed discrepancy. -/
theorem exists_orientation_with_offset {I : Type*} (A B : I → Label)
    (surjective : Function.Surjective A) (k : Label) :
    ∃ reverse : Bool, ∃ i j, fused A B reverse i + k ≠ fused A B reverse j + k := by
  obtain ⟨r,i,j,h⟩ := exists_orientation A B surjective
  exact ⟨r,i,j,fun eq => h (add_right_cancel eq)⟩

/-- In particular this applies to arbitrary label permutations, not only linear ones. -/
theorem permutations (A B : Equiv.Perm Label) :
    ∃ reverse : Bool, ∃ i j, fused A B reverse i ≠ fused A B reverse j :=
  exists_orientation A B A.surjective

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticOrientation
