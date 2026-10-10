import Holant.Proofs.Hardness.GeneralEOARSSupport

/-! The reducible branch in the mating argument is retained explicitly.
If each coordinate has an independent opposite partner, the support is
ternary-XOR closed. No tensor factor is asserted to be an available gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedSupport
open Holant Holant.Tractable
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def toggle (i j : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun k => if k = i ∨ k = j then !(x k) else x k

def FreePair (f : Signature AlgebraicComplex n) (i j : Fin n) : Prop :=
  i ≠ j ∧ (∀ x, f x ≠ 0 → x i ≠ x j) ∧
    ∀ x, f x ≠ 0 → f (toggle i j x) ≠ 0

def mismatches (x y : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ y i)

@[simp] theorem mem_mismatches (x y : Fin n → Bool) (i : Fin n) :
    i ∈ mismatches x y ↔ x i ≠ y i := by simp [mismatches]

theorem opposite_triple (a b c : Fin n → Bool) (i j : Fin n)
    (ha : a i ≠ a j) (hb : b i ≠ b j) (hc : c i ≠ c j) :
    tripleXor a b c i ≠ tripleXor a b c j := by
  cases hai : a i <;> cases haj : a j <;>
    cases hbi : b i <;> cases hbj : b j <;>
    cases hci : c i <;> cases hcj : c j <;> simp_all [tripleXor]

theorem partner_mismatch (x w : Fin n → Bool) (i j : Fin n)
    (hx : x i ≠ x j) (hw : w i ≠ w j) (hi : x i ≠ w i) : x j ≠ w j := by
  cases hxi : x i <;> cases hxj : x j <;>
    cases hwi : w i <;> cases hwj : w j <;> simp_all

theorem toggle_decreases (x w : Fin n → Bool) (i j : Fin n)
    (hi : x i ≠ w i) (hj : x j ≠ w j) :
    (mismatches (toggle i j x) w).card < (mismatches x w).card := by
  have flip_i : Bool.not (x i) = w i := by cases hxi : x i <;> cases hwi : w i <;> simp_all
  have flip_j : Bool.not (x j) = w j := by cases hxj : x j <;> cases hwj : w j <;> simp_all
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    have hk' := (mem_mismatches _ _ k).mp hk
    by_cases hki : k = i
    · subst k
      simp [toggle,flip_i] at hk'
    · by_cases hkj : k = j
      · subst k
        simp [toggle,flip_j] at hk'
      · exact (mem_mismatches _ _ k).mpr (by simpa [toggle,hki,hkj] using hk')
  · intro h
    have hi' : i ∈ mismatches (toggle i j x) w :=
      h.symm ▸ (mem_mismatches x w i).mpr hi
    simpa [toggle,flip_i] using hi'

theorem closed_of_free_partners (f : Signature AlgebraicComplex n)
    (partners : ∀ i, ∃ j, FreePair f i j) : GeneralEONegativeClosedSupport.Closed f := by
  classical
  intro a b c ha hb hc
  let w := tripleXor a b c
  let S : Finset (Fin n → Bool) := Finset.univ.filter (fun x => f x ≠ 0)
  have hS : S.Nonempty := ⟨a,by simpa [S] using ha⟩
  obtain ⟨x,hx,hmin⟩ := S.exists_min_image (fun x => (mismatches x w).card) hS
  have hfx : f x ≠ 0 := by simpa [S] using hx
  have equal : x = w := by
    by_contra hne
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ w i := by
      by_contra h
      apply hne
      funext i
      exact not_ne_iff.mp (fun hi => h ⟨i,hi⟩)
    obtain ⟨j,_,hop,hfree⟩ := partners i
    have hw : w i ≠ w j := opposite_triple a b c i j (hop a ha) (hop b hb) (hop c hc)
    have hj : x j ≠ w j := partner_mismatch x w i j (hop x hfx) hw hi
    have hy : toggle i j x ∈ S := by simpa [S] using hfree x hfx
    exact (not_lt_of_ge (hmin _ hy)) (toggle_decreases x w i j hi hj)
  change f w ≠ 0
  rwa [← equal]

theorem nonclosed_port (f : Signature AlgebraicComplex n)
    (h : ¬GeneralEONegativeClosedSupport.Closed f) :
    ∃ i, ∀ j, ¬FreePair f i j := by
  classical
  by_contra hh
  apply h
  apply closed_of_free_partners
  simpa only [not_exists,not_forall,not_not] using hh

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedSupport
