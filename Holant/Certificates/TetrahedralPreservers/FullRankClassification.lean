import Holant.Certificates.TetrahedralPreservers.IdentityStabilizer
import Holant.Certificates.TetrahedralPreservers.FullRankData

/-! Unrestricted rank-four classification: every arbitrary complex preserver
is a scalar times one of 12 left translations times 48 signed stabilizers. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

theorem oneSided_smul {S : Set V} (hS : Saturated S) {A : End} (hA : OneSided S A)
    (c : ℂ) : OneSided S (c • A) := by
  intro r hr
  rw [Matrix.smul_mulVec]
  by_cases hc : c=0
  · simp [hc]
  rcases hA r hr with h | h
  · simp [h]
  · exact Or.inr (hS h hc)

theorem twoSided_smul {S : Set V} (hS : Saturated S) {A : End} (hA : TwoSided S A)
    (c : ℂ) : TwoSided S (c • A) := by
  exact ⟨oneSided_smul hS hA.1 c,by rw [sharp_smul]; exact oneSided_smul hS hA.2 c⟩

theorem leftMap_first (k : Fin 12) : leftMap k *ᵥ Pi.single (0 : Fin 4) 1 = standardPoint k := by
  rw [← lift_zstandard,Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [leftMap,liftMatrix,leftRaw,liftVector]

theorem signedMap_first (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    signedMap σ ε *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1 := by
  rw [Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> norm_num [signedMap,liftMatrix,signedRaw,Pi.single_apply]

theorem signedMap_axis (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (j : Fin 3) :
    signedMap σ ε *ᵥ Pi.single j.succ 1 = (signBit (ε j) : ℂ) • Pi.single (σ j).succ 1 := by
  rw [Matrix.mulVec_single_one]
  ext i
  cases hε : ε j <;> simp [signedMap,liftMatrix,signedRaw,zsign,signBit,Pi.single_apply,hε]

theorem fixed_identity_eq_signedMap (A : End) (hA : A.det ≠ 0)
    (h : OneSided Standard A) (h0 : A *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1) :
    ∃ σ : Equiv.Perm (Fin 3), ∃ ε : Fin 3 → Bool, A = signedMap σ ε := by
  obtain ⟨σ,ε,he⟩ := fixed_identity_signed_permutation A hA h h0
  refine ⟨σ,ε,?_⟩
  ext i j
  have hcol : A *ᵥ Pi.single j 1 = signedMap σ ε *ᵥ Pi.single j 1 := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [h0,signedMap_first]
    · rw [he,signedMap_axis]
  simpa using congrFun hcol i

theorem standard_full_rank_complete (A : End) (hA : A.rank=4) (h : OneSided Standard A) :
    ∃ k : Fin 12, ∃ σ : Equiv.Perm (Fin 3), ∃ ε : Fin 3 → Bool, ∃ c : ℂ,
      c ≠ 0 ∧ A = c • (leftMap k * signedMap σ ε) := by
  have hdet := (rank_four_iff_det_ne_zero A).mp hA
  have hi := Matrix.mulVec_injective_of_det_ne_zero hdet
  have hfirst : A *ᵥ Pi.single (0 : Fin 4) 1 ∈ Standard := by
    rcases h _ (standard_axis 0) with hz | hm
    · have hh := hi (show A *ᵥ Pi.single (0 : Fin 4) 1 = A *ᵥ 0 by simpa using hz)
      have hh' := congrFun hh 0
      simp at hh'
    · exact hm
  obtain ⟨k,c,hc,he⟩ := (standard_iff _).mp hfirst
  have hL : (leftMap k).det ≠ 0 := (rank_four_iff_det_ne_zero _).mp (leftMap_rank k)
  have hLi : (leftMap k)⁻¹.det ≠ 0 := by
    rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact inv_ne_zero hL
  let B : End := c⁻¹ • ((leftMap k)⁻¹ * A)
  have hBdet : B.det ≠ 0 := by
    dsimp [B]
    rw [Matrix.det_smul,Matrix.det_mul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) (mul_ne_zero hLi hdet)
  have hB : OneSided Standard B :=
    oneSided_smul standard_saturated
      (oneSided_comp (standard_inverse_oneSided _ hL (leftMap_twoSided k).1) h) c⁻¹
  have hB0 : B *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1 := by
    simp only [B,Matrix.smul_mulVec,← Matrix.mulVec_mulVec]
    rw [he,← leftMap_first k,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hL),Matrix.one_mulVec,
      smul_smul,inv_mul_cancel₀ hc,one_smul]
  obtain ⟨σ,ε,hBe⟩ := fixed_identity_eq_signedMap B hBdet hB hB0
  refine ⟨k,σ,ε,c,hc,?_⟩
  calc
    A = c • (leftMap k * B) := by
      simp only [B,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ hc,one_smul]
      rw [← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL),Matrix.one_mul]
    _ = c • (leftMap k * signedMap σ ε) := by rw [hBe]

def FullIndex := Fin 12 × Equiv.Perm (Fin 3) × (Fin 3 → Bool)
def fullMap (i : FullIndex) : End := leftMap i.1 * signedMap i.2.1 i.2.2

theorem fullMap_twoSided (i : FullIndex) : TwoSided Standard (fullMap i) :=
  twoSided_comp (leftMap_twoSided i.1) (signedMap_twoSided i.2.1 i.2.2)

theorem fullMap_rank (i : FullIndex) : (fullMap i).rank=4 := by
  rw [fullMap,Matrix.rank_mul_eq_right_of_det_ne_zero _ _
    ((rank_four_iff_det_ne_zero _).mp (leftMap_rank _)),signedMap_rank]

theorem standard_full_rank_twoSided (A : End) (hA : A.rank=4) :
    TwoSided Standard A ↔ ∃ i : FullIndex, ∃ c : ℂ, c ≠ 0 ∧ A=c • fullMap i := by
  constructor
  · intro h
    obtain ⟨k,σ,ε,c,hc,he⟩ := standard_full_rank_complete A hA h.1
    exact ⟨⟨k,σ,ε⟩,c,hc,he⟩
  · rintro ⟨i,c,hc,rfl⟩
    exact twoSided_smul standard_saturated (fullMap_twoSided i) c

end Holant.Certificates.TetrahedralPreservers
