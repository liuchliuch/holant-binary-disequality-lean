import Holant.Dihedral.SectorRuling.SegreAlgebra

/-! Phase selection retains every zero and proportional case. A nonzero
pencil on at least three distinct phases has two distinct nonzero samples. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Marked Holant.Certificates Holant.Dihedral.CompatibleClosure

private theorem grid_other {m : ℕ} [NeZero m] (hm : 3 ≤ m) (i : Grid m) : ∃ j : Grid m,j ≠ i := by
  classical
  have hc : ({i} : Finset (Grid m)).card < (Finset.univ : Finset (Grid m)).card := by
    simp only [Finset.card_singleton,Finset.card_univ,grid_card]
    omega
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨j,by simpa using hj⟩

private theorem grid_third {m : ℕ} [NeZero m] (hm : 3 ≤ m) (i j : Grid m) :
    ∃ k : Grid m,k ≠ i ∧ k ≠ j := by
  classical
  have hc : ({i,j} : Finset (Grid m)).card < (Finset.univ : Finset (Grid m)).card := by
    have hh := Finset.card_insert_le i ({j} : Finset (Grid m))
    simp only [Finset.card_singleton,Finset.card_univ,grid_card] at hh ⊢
    omega
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨k,by simpa using hk⟩

theorem third_root {m : ℕ} (hm : 3 ≤ m) (a b : Scalar) (ha : Roots m a) (hb : Roots m b) :
    ∃ c : Scalar,Roots m c ∧ c ≠ a ∧ c ≠ b := by
  classical
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨i,hi⟩ := gridValue_surjective a ha
  obtain ⟨j,hj⟩ := gridValue_surjective b hb
  obtain ⟨k,hki,hkj⟩ := grid_third hm i j
  exact ⟨gridValue k,gridValue_roots k,
    fun h => hki (gridValue_injective (h.trans hi.symm)),
    fun h => hkj (gridValue_injective (h.trans hj.symm))⟩

theorem tensor_interpolation {n : ℕ} (U V : Signature Scalar n) (a b t : Scalar) (hab : a ≠ b) :
    tensorPencil U V t=combination ((b-t)/(b-a)) ((t-a)/(b-a)) (tensorPencil U V a) (tensorPencil U V b) := by
  funext x
  simp only [tensorPencil,combination]
  field_simp [sub_ne_zero.mpr (Ne.symm hab)]
  ring

theorem tensor_two_zeros {n : ℕ} (U V : Signature Scalar n) (a b : Scalar) (hab : a ≠ b)
    (ha : tensorPencil U V a=0) (hb : tensorPencil U V b=0) : U=0 ∧ V=0 := by
  have hv : V=0 := by
    funext x
    have h₀ := congrFun ha x
    have h₁ := congrFun hb x
    change U x+a*V x=0 at h₀
    change U x+b*V x=0 at h₁
    have hh : (a-b)*V x=0 := by linear_combination h₀-h₁
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hab)
  refine ⟨?_,hv⟩
  funext x
  have h := congrFun ha x
  simpa [tensorPencil,hv] using h

theorem two_nonzero_samples {m n : ℕ} (hm : 3 ≤ m) (U V : Signature Scalar n)
    (a : Scalar) (ha : Roots m a) (hna : tensorPencil U V a ≠ 0) :
    ∃ b : Scalar,Roots m b ∧ a ≠ b ∧ tensorPencil U V b ≠ 0 := by
  classical
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨i,hi⟩ := gridValue_surjective a ha
  obtain ⟨j,hji⟩ := grid_other hm i
  have hab : a ≠ gridValue j := fun h => hji (gridValue_injective (h.symm.trans hi.symm))
  by_cases hj : tensorPencil U V (gridValue j)=0
  · obtain ⟨k,hki,hkj⟩ := grid_third hm i j
    have hak : a ≠ gridValue k := fun h => hki (gridValue_injective (h.symm.trans hi.symm))
    refine ⟨gridValue k,gridValue_roots k,hak,?_⟩
    intro hk
    have hτ : gridValue j ≠ gridValue k := fun h => hkj (gridValue_injective h).symm
    obtain ⟨hU,hV⟩ := tensor_two_zeros U V _ _ hτ hj hk
    exact hna (by funext x; simp [tensorPencil,hU,hV])
  · exact ⟨gridValue j,gridValue_roots j,hab,hj⟩

theorem MatchingSample.nonzero {m s : ℕ} (hm : 0<m) {q : Signature Scalar (2*s)}
    (hq : MatchingSample m s q) : q ≠ 0 := by
  obtain ⟨p,A,κ,hA,hκ,rfl⟩ := hq
  exact productValue_nonzero p A (fun e => groupM_isMonomial hm (hA e)) hκ

end Holant.Dihedral.SectorRuling
