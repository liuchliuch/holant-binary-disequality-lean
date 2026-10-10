import Holant.Certificates.TetrahedralPreservers.StandardGeometry

/-! The key unrestricted stabilizer step: an invertible preserver fixing the
identity direction must permute the three other quaternion axes. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

theorem fixed_identity_axes (A : End) (hA : A.det ≠ 0) (h : OneSided Standard A)
    (h0 : A *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1) (i : Fin 3) :
    ∃ j : Fin 3, ∃ c : ℂ, c ≠ 0 ∧
      A *ᵥ Pi.single i.succ 1 = c • Pi.single j.succ 1 := by
  have hi := Matrix.mulVec_injective_of_det_ne_zero hA
  have hinv := standard_inverse_oneSided A hA h
  have hi0 : A⁻¹ *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1 := by
    have hh := congrArg (fun r : V => A⁻¹ *ᵥ r) h0
    simpa only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec] using hh.symm
  have himg : A *ᵥ Pi.single i.succ 1 ∈ Standard := by
    rcases h _ (standard_axis i.succ) with hz | hm
    · have hh := hi (show A *ᵥ Pi.single i.succ 1 = A *ᵥ 0 by simpa using hz)
      have hh' := congrFun hh i.succ
      simp at hh'
    · exact hm
  obtain ⟨k,c,hc,hk⟩ := (standard_iff _).mp himg
  rcases standard_axis_or_full k with ⟨j,rfl⟩ | hfull
  · rw [standardPoint_axis] at hk
    have hj : j ≠ 0 := by
      intro hj
      subst j
      have hh : A *ᵥ Pi.single i.succ 1 = A *ᵥ (c • Pi.single (0 : Fin 4) 1) := by
        rw [Matrix.mulVec_smul,h0,hk]
      have hh' := congrFun (hi hh) i.succ
      simp [Pi.single_apply,Fin.succ_ne_zero] at hh'
    obtain ⟨j,rfl⟩ := Fin.eq_succ_of_ne_zero hj
    exact ⟨j,c,hc,hk⟩
  · have hik : A⁻¹ *ᵥ standardPoint k = c⁻¹ • Pi.single i.succ 1 := by
      have hh := congrArg (fun r : V => A⁻¹ *ᵥ r) hk
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
        Matrix.one_mulVec,Matrix.mulVec_smul] at hh
      rw [hh,smul_smul,inv_mul_cancel₀ hc,one_smul]
    have hcomp : A⁻¹ *ᵥ standardPoint (complementIndex k) ∈ Standard := by
      rcases hinv _ (standardPoint_mem _) with hz | hm
      · have hh := congrArg (fun r : V => A *ᵥ r) hz
        rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
          Matrix.one_mulVec,Matrix.mulVec_zero] at hh
        exact False.elim (standardPoint_ne_zero _ hh)
      · exact hm
    rw [standard_complement k hfull,Matrix.mulVec_sub,Matrix.mulVec_smul,hi0,hik] at hcomp
    apply False.elim
    apply no_two_support i (by norm_num : (2 : ℂ) ≠ 0) (neg_ne_zero.mpr (inv_ne_zero hc))
    simpa only [sub_eq_add_neg,neg_smul] using hcomp

theorem fixed_identity_axis_permutation (A : End) (hA : A.det ≠ 0)
    (h : OneSided Standard A) (h0 : A *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ c : Fin 3 → ℂ, (∀ i, c i ≠ 0) ∧
      ∀ i, A *ᵥ Pi.single i.succ 1 = c i • Pi.single (σ i).succ 1 := by
  choose σ c hc he using fixed_identity_axes A hA h h0
  have hi := Matrix.mulVec_injective_of_det_ne_zero hA
  have hσ : Function.Injective σ := by
    intro i j hij
    have heq : A *ᵥ Pi.single i.succ 1 = (c i * (c j)⁻¹) • (A *ᵥ Pi.single j.succ 1) := by
      rw [he i,he j,hij,smul_smul]
      congr 1
      field_simp [hc j]
    rw [← Matrix.mulVec_smul] at heq
    have hp := hi heq
    by_contra hn
    have hs : i.succ ≠ j.succ := fun he => hn (Fin.succ_inj.mp he)
    have hentry := congrFun hp i.succ
    simp [Pi.single_apply,hs,Ne.symm hs] at hentry
  exact ⟨Equiv.ofBijective σ ⟨hσ,Finite.surjective_of_injective hσ⟩,c,hc,he⟩

/-- Even the column scalars are forced: only the 3! times 2^3 signed
permutations occur in the identity-fixing stabilizer. -/
theorem fixed_identity_signed_permutation (A : End) (hA : A.det ≠ 0)
    (h : OneSided Standard A) (h0 : A *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ ε : Fin 3 → Bool,
      ∀ i, A *ᵥ Pi.single i.succ 1 = (signBit (ε i) : ℂ) • Pi.single (σ i).succ 1 := by
  obtain ⟨σ,c,hc,he⟩ := fixed_identity_axis_permutation A hA h h0
  have hcol0 (j : Fin 4) : A j 0 = (Pi.single (0 : Fin 4) (1 : ℂ) : V) j := by
    simpa using congrFun h0 j
  have hcol (j : Fin 4) (k : Fin 3) : A j k.succ = c k * (Pi.single (σ k).succ (1 : ℂ) : V) j := by
    simpa using congrFun (he k) j
  let w : V := A *ᵥ (fun _ => 1)
  have hw0 : w 0=1 := by
    change (∑ j : Fin 4, A 0 j * 1)=1
    simp only [mul_one]
    rw [Fin.sum_univ_succ,hcol0]
    simp_rw [hcol]
    simp [Pi.single_apply,Fin.succ_ne_zero]
  have hw (i : Fin 3) : w (σ i).succ=c i := by
    change (∑ j : Fin 4, A (σ i).succ j * 1)=c i
    simp only [mul_one]
    rw [Fin.sum_univ_succ,hcol0]
    simp_rw [hcol]
    simp [Pi.single_apply,Fin.succ_ne_zero]
  have hwS : w ∈ Standard := by
    have hones : (fun _ : Fin 4 => (1 : ℂ)) ∈ Standard := by
      have hh := standardPoint_mem 4
      rw [standardPoint_table] at hh
      have he : standardTable 4 = (fun _ : Fin 4 => (1 : ℂ)) := by
        ext i; fin_cases i <;> rfl
      rwa [he] at hh
    rcases h _ hones with hz | hm
    · have hh := congrFun hz 0
      change w 0=0 at hh
      rw [hw0] at hh
      exact False.elim (one_ne_zero hh)
    · exact hm
  have hsign (i : Fin 3) : ∃ ε : Bool, c i = (signBit ε : ℂ) := by
    have hi := standard_coordinate_signs hwS hw0
      ⟨(σ i).succ,Fin.succ_ne_zero _,by rw [hw i]; exact hc i⟩ (σ i).succ
    rw [hw i] at hi
    rcases hi with hi | hi
    · exact ⟨false,by simpa [signBit] using hi⟩
    · exact ⟨true,by simpa [signBit] using hi⟩
  choose ε hε using hsign
  exact ⟨σ,ε,fun i => by rw [he i,hε i]⟩

end Holant.Certificates.TetrahedralPreservers
