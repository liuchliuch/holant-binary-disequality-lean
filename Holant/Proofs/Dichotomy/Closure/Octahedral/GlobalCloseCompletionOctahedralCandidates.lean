import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralNormalization

/-! Coefficient extraction from the preserved marked-octahedral proof. Actual 24*24*2 candidate COVERAGE. The second index
is the old literal quaternion normalizer dictionary, consumed from the
already proved normal_identity. Coverage is proved from the arbitrary-map
stabilizer, not inferred from slot count or an enum-complete assumption.
Exact projective distinctness/count is deliberately a separate obligation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open scoped BigOperators Matrix

theorem qMatrix_zOcta (k : Fin 24) : qMatrix (zOcta k) = kernel 0 k := by
  rw [qMatrix,←point_zero_table]
  change assemble (quaternionCoefficient (kernel 0 k)) = kernel 0 k
  exact assemble_coefficient _

theorem kernel_inverse (k : Fin 24) : (kernel 0 k)⁻¹ =
    (zNorm (zOcta k) : ℂ)⁻¹ • qMatrix (zConj (zOcta k)) := by
  have hn : (zNorm (zOcta k) : ℂ) ≠ 0 := by exact_mod_cast zOcta_norm_ne_zero k
  apply Matrix.inv_eq_right_inv
  rw [←qMatrix_zOcta,Matrix.mul_smul,qMatrix_conjugate,smul_smul,inv_mul_cancel₀ hn,one_smul]

/-- The old signed stabilizer's normalizing binary is an actual entry of
the original 24 standard dictionary. No arbitrary normalizer is selected. -/
theorem signedMap_dictionary (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    signedMap σ ε = kindSandwich (normalTranspose σ ε)
      (kernel 0 (normalIndexTable (normalCode σ ε)))
      (kernel 0 (normalIndexTable (normalCode σ ε)))⁻¹ := by
  let k := normalIndexTable (normalCode σ ε)
  let n : ℂ := zNorm (zOcta k)
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast zOcta_norm_ne_zero k
  have he := congrArg liftMatrix (normal_identity σ ε)
  rw [liftMatrix_mul,liftMatrix_mul,liftMatrix_smul,lift_zLeft,lift_zRight,lift_zTranspose,
    sandwich_comp,sandwich_kind_comp] at he
  simp only [Matrix.mul_one,Matrix.one_mul] at he
  change kindSandwich (normalTranspose σ ε) (qMatrix (zOcta k))
    (qMatrix (zConj (zOcta k))) = n • signedMap σ ε at he
  symm
  change kindSandwich (normalTranspose σ ε) (kernel 0 k) (kernel 0 k)⁻¹ = _
  rw [kernel_inverse,←qMatrix_zOcta,kindSandwich_smul_right,he,
    smul_smul,inv_mul_cancel₀ hn,one_smul]

def CandidateIndex := Fin 24 × Fin 24 × Bool
def standardCandidate (i : CandidateIndex) : End :=
  left24 i.1 * kindSandwich i.2.2 (kernel 0 i.2.1) (kernel 0 i.2.1)⁻¹

theorem candidateIndex_card : Nat.card CandidateIndex = 1152 := by
  change Nat.card (Fin 24 × Fin 24 × Bool) = 1152
  rw [Nat.card_eq_fintype_card]
  norm_num

/-- Complete coverage of all arbitrary full-rank standard-root preservers.
The exact finite indices and the nonzero multiplier are internally found. -/
theorem candidate_coverage (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots 0) A) :
    ∃ i : CandidateIndex, ∃ c : ℂ, c ≠ 0 ∧ A = c • standardCandidate i := by
  obtain ⟨k,σ,ε,c,hc,he⟩ := standard_full_rank_complete A hd h
  exact ⟨(k,normalIndexTable (normalCode σ ε),normalTranspose σ ε),c,hc,
    by simpa only [standardCandidate,signedMap_dictionary] using he⟩

/-- Each literal slot, with its actual nonzero image scalar, already has
the required nonsingular two-sided binary formula. Root safety is not a
caller premise, nor is a proposed normal form supplied to the source. -/
theorem standardCandidate_normal_forms (i : CandidateIndex) (c : ℂ) (hc : c ≠ 0) :
    ∃ U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      (c • standardCandidate i = sandwich U W ∨
        c • standardCandidate i = transposeSandwich U W) := by
  have hleft : (kernel 0 i.1).det ≠ 0 := (Direction.standard 0 i.1).det_ne_zero
  have hright : (kernel 0 i.2.1).det ≠ 0 := (Direction.standard 0 i.2.1).det_ne_zero
  refine ⟨c • (kernel 0 i.1*kernel 0 i.2.1),(kernel 0 i.2.1)⁻¹,?_,?_,?_⟩
  · rw [Matrix.det_smul,Matrix.det_mul]
    exact mul_ne_zero (pow_ne_zero _ hc) (mul_ne_zero hleft hright)
  · rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact inv_ne_zero hright
  · rw [standardCandidate,left24,sandwich_kind_comp,Matrix.mul_one,
      ←kindSandwich_smul_left]
    cases hb : i.2.2 <;> simp [kindSandwich,hb]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
