import Holant.Certificates.RainbowOrbit.FactorUniqueness

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem B_matrix : B=P1 (1 : BinaryMatrix) (1 : BinaryMatrix) := by
  simp only [B,Q0_matrix]

/-- The actual swap-rank-one theorem forces the last free binary to be scalar.
The coefficients of the three collinear points are retained exactly. -/
theorem normalized_rank_one (W : BinaryMatrix) (α β : ℂ) (hα : α≠0) (hβ : β≠0)
    (hr : (flatten2 (α • A+β • P1 (1 : BinaryMatrix) W)).rank=1) :
    W=(-α/β) • (1 : BinaryMatrix) ∧
    α • A+β • P1 (1 : BinaryMatrix) W=α • C := by
  let k : ℂ := -β/α
  have hk : k≠0 := div_ne_zero (neg_ne_zero.mpr hβ) hα
  have he : α • (A-P1 (1 : BinaryMatrix) (k • W))=
      α • A+β • P1 (1 : BinaryMatrix) W := by
    funext x
    simp only [Pi.smul_apply,Pi.sub_apply,Pi.add_apply,P1,Matrix.smul_apply,smul_eq_mul]
    dsimp [k]
    field_simp
    <;> ring
  have hr' : (flatten2 (A-P1 (1 : BinaryMatrix) (k • W))).rank=1 := by
    have hh := hr
    rw [←he] at hh
    change (flatten 2 (α • (A-P1 (1 : BinaryMatrix) (k • W)))).rank=1 at hh
    rw [flatten_smul,Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero hα)] at hh
    exact hh
  have hw : k • W=(1 : BinaryMatrix) := by
    simpa using matching1_first_inverse (1 : BinaryMatrix) (k • W) (by simp) hr'
  constructor
  · calc W=k⁻¹ • (k • W) := by simp [smul_smul,hk]
      _=k⁻¹ • (1 : BinaryMatrix) := by rw [hw]
      _=(-α/β) • (1 : BinaryMatrix) := by congr 1; dsimp [k]; field_simp
  · rw [←he,hw,←B_matrix,A_sub_B]

def normalization (U V S : BinaryMatrix) : Legs :=
  fun j => secondNormalization (U⁻¹*S*V⁻¹.transpose) j * firstNormalization U V j

theorem firstNormalization_det (U V : BinaryMatrix) (hU : U.det≠0) (hV : V.det≠0) :
    ∀j,(firstNormalization U V j).det≠0 := by
  intro j
  fin_cases j <;> simp [firstNormalization,Matrix.det_nonsing_inv,hU,hV]

theorem secondNormalization_det (U : BinaryMatrix) (hU : U.det≠0) :
    ∀j,(secondNormalization U j).det≠0 := by
  intro j
  fin_cases j <;> simp [secondNormalization,Matrix.det_nonsing_inv,hU]

theorem normalization_det (U V S : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0) (hS : S.det≠0) :
    ∀j,(normalization U V S j).det≠0 := by
  have hs : (U⁻¹*S*V⁻¹.transpose).det≠0 := by
    simp [Matrix.det_mul,Matrix.det_nonsing_inv,hU,hV,hS]
  intro j
  exact by simpa [normalization,Matrix.det_mul] using
    mul_ne_zero (secondNormalization_det _ hs j) (firstNormalization_det U V hU hV j)

/-- A literal ordered normalization of any three invertible matching tensors
on a projective line. No finite group or candidate-coverage hypothesis is used. -/
theorem normalize_rainbow (U V S T M N : BinaryMatrix)
    (hU : U.det≠0) (hV : V.det≠0) (hS : S.det≠0) (hM : M.det≠0) (hN : N.det≠0)
    (α β : ℂ) (hα : α≠0) (hβ : β≠0)
    (hline : P2 M N=α • P0 U V+β • P1 S T) :
    act (normalization U V S) (P0 U V)=A ∧
    act (normalization U V S) (P1 S T)=(-α/β) • B ∧
    act (normalization U V S) (P2 M N)=α • C := by
  let S' : BinaryMatrix := U⁻¹*S*V⁻¹.transpose
  have hs : S'.det≠0 := by dsimp [S']; simp [Matrix.det_mul,Matrix.det_nonsing_inv,hU,hV,hS]
  have h0 : act (normalization U V S) (P0 U V)=A := by
    unfold normalization
    rw [←act_comp,firstNormalization_A U V hU hV,secondNormalization_A _ hs]
  have h1 : act (normalization U V S) (P1 S T)=P1 (1 : BinaryMatrix) (S'.transpose*T) := by
    unfold normalization
    rw [←act_comp,firstNormalization_P1,secondNormalization_P1 _ _ hs]
  have h2 : act (normalization U V S) (P2 M N)=α • A+β • P1 (1 : BinaryMatrix) (S'.transpose*T) := by
    rw [hline,act_add,act_smul,act_smul,h0,h1]
  have hr : (flatten2 (act (normalization U V S) (P2 M N))).rank=1 := by
    have hh := OctahedralSeparator.flatten_rank_coordinateAction (normalization U V S)
      (P2 M N) (normalization_det U V S hU hV hS) 2
    have hm := matching_flattening_rank 2 2 M N hM hN
    simpa [act,flatten,matchingTensor] using hh.trans hm
  rw [h2] at hr
  obtain ⟨hw,hc⟩ := normalized_rank_one _ α β hα hβ hr
  refine ⟨h0,?_,h2.trans hc⟩
  rw [h1,hw,B_matrix]
  funext x
  simp [P1,Matrix.smul_apply,smul_eq_mul]
  ring

end
end Holant.Certificates.RainbowOrbit
