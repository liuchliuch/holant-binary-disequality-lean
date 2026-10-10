import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralIdentity

/-! Coefficient extraction from the preserved marked-octahedral proof. All arbitrary invertible standard F4 root preservers
are internally normalized by one of the actual 24 left translations.
The new identity-stabilizer proof then covers the actual 48 signed maps.
No enumeration-completeness or normal-form premise is accepted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open scoped BigOperators Matrix

theorem sandwich_one : sandwich 1 1 = (1 : End) := by
  apply matrix_ext_action
  intro v
  rw [sandwich_action,Matrix.one_mul,Matrix.mul_one,Matrix.one_mulVec]
  exact coefficient_assemble v

def left24 (k : Fin 24) : End := sandwich (kernel 0 k) 1

theorem left24_safe (k : Fin 24) : OneSided (Roots 0) (left24 k) := by
  intro v hv
  have hV : Direction 0 (assemble v) := (mem_coefficientSet_iff _ v).mp hv
  rw [left24,sandwich_action,Matrix.mul_one]
  exact Or.inr ⟨_,direction_mul (Direction.standard 0 k) hV,rfl⟩

theorem left24_det (k : Fin 24) : (left24 k).det ≠ 0 := by
  have hd : (kernel 0 k).det ≠ 0 := (Direction.standard 0 k).det_ne_zero
  have he : sandwich (kernel 0 k)⁻¹ 1 * left24 k = 1 := by
    rw [left24,sandwich_comp,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.one_mul,sandwich_one]
  have hh := congrArg Matrix.det he
  rw [Matrix.det_mul,Matrix.det_one] at hh
  intro hz
  rw [hz,mul_zero] at hh
  exact zero_ne_one hh

theorem left24_first (k : Fin 24) :
    left24 k *ᵥ Pi.single (0 : Fin 4) 1 = point 0 k := by
  have h0 : assemble (Pi.single (0 : Fin 4) 1) = (1 : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) := by
    rw [←coordinates_basis 0]
    change assemble (quaternionCoefficient (Matrix.of (quaternionBasis 0))) = 1
    rw [assemble_coefficient]
    ext a b
    cases a <;> cases b <;> simp [quaternionBasis,Q0,Holant.Signature.equality,Matrix.one_apply]
  rw [left24,sandwich_action,h0,Matrix.mul_one,Matrix.mul_one]
  rfl

theorem standard_full_rank_complete (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots 0) A) :
    ∃ k : Fin 24, ∃ σ : Equiv.Perm (Fin 3), ∃ ε : Fin 3 → Bool, ∃ c : ℂ,
      c ≠ 0 ∧ A = c • (left24 k*signedMap σ ε) := by
  let p := rootAction 0 A hd h
  let k := p.perm 0
  let c := p.scale 0
  have hc : c ≠ 0 := p.scale_ne_zero 0
  have first : A *ᵥ Pi.single (0 : Fin 4) 1 = c • point 0 k := by
    have hz : point 0 (0 : Fin 24)=Pi.single (0 : Fin 4) 1 := point_zero_axis 0
    simpa only [hz] using p.image_eq 0
  have hL := left24_det k
  have hLi : ((left24 k)⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact inv_ne_zero hL
  let B : End := c⁻¹ • ((left24 k)⁻¹*A)
  have hBd : B.det ≠ 0 := by
    dsimp [B]
    rw [Matrix.det_smul,Matrix.det_mul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) (mul_ne_zero hLi hd)
  have hB : OneSided (Roots 0) B :=
    oneSided_smul (roots_saturated 0)
      (oneSided_comp (inverse_oneSided 0 _ hL (left24_safe k)) h) c⁻¹
  have hB0 : B *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1 := by
    simp only [B,Matrix.smul_mulVec,←Matrix.mulVec_mulVec]
    rw [first,←left24_first k,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hL),Matrix.one_mulVec,
      smul_smul,inv_mul_cancel₀ hc,one_smul]
  obtain ⟨σ,ε,hBe⟩ := fixed_identity_complete B hBd hB hB0
  refine ⟨k,σ,ε,c,hc,?_⟩
  calc
    A = c • (left24 k*B) := by
      simp only [B,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ hc,one_smul]
      rw [←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hL),Matrix.one_mul]
    _ = _ := by rw [hBe]

/-- This finite index has exactly 24*3!*2^3=1152 slots; map coverage is
proved above separately, not inferred from this cardinality. -/
def SignedCandidateIndex := Fin 24 × Equiv.Perm (Fin 3) × (Fin 3 → Bool)
def signedCandidate (i : SignedCandidateIndex) : End := left24 i.1*signedMap i.2.1 i.2.2

theorem signedCandidateIndex_card : Nat.card SignedCandidateIndex = 1152 := by
  change Nat.card (Fin 24 × Equiv.Perm (Fin 3) × (Fin 3 → Bool)) = 1152
  rw [Nat.card_eq_fintype_card]
  norm_num [SignedCandidateIndex,Fintype.card_prod,Fintype.card_fun,Fintype.card_perm,Nat.factorial]

theorem standard_full_rank_normal_forms (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots 0) A) :
    ∃ U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      (A = sandwich U W ∨ A = transposeSandwich U W) := by
  obtain ⟨k,σ,ε,c,hc,rfl⟩ := standard_full_rank_complete A hd h
  obtain ⟨U,W,hU,hW,he⟩ := signedMap_normal_form σ ε
  have hk : (kernel 0 k).det ≠ 0 := (Direction.standard 0 k).det_ne_zero
  refine ⟨c • (kernel 0 k*U),W,?_,hW,?_⟩
  · rw [Matrix.det_smul,Matrix.det_mul]
    exact mul_ne_zero (pow_ne_zero _ hc) (mul_ne_zero hk hU)
  · change c • (left24 k*signedMap σ ε) = sandwich _ _ ∨
      c • (left24 k*signedMap σ ε) = transposeSandwich _ _
    rw [left24,he,sandwich_kind_comp,Matrix.mul_one,←kindSandwich_smul_left]
    cases hb : normalTranspose σ ε <;> simp [kindSandwich,hb]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
