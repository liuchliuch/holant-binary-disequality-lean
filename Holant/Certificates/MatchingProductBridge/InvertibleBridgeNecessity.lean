import Holant.Certificates.MatchingProductBridge.InvertibleBridgeCone
import Holant.Certificates.MatchingProductBridge.InvertibleBridgeSimple

namespace Holant.Certificates.MatchingProductBridge
open Matrix
open scoped Kronecker
noncomputable section

theorem matrix_rank_neg (M : PairMatrix) : (-M).rank = M.rank := by
  have he : -M = (-1:ℂ) • M := by module
  rw [he]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors M (mem_nonZeroDivisors_of_ne_zero (by norm_num))

private theorem flatten0_sub (X Y : FourTensor) : flatten0 (X-Y)=flatten0 X-flatten0 Y := rfl
private theorem flatten1_sub (X Y : FourTensor) : flatten1 (X-Y)=flatten1 X-flatten1 Y := rfl
private theorem flatten2_sub (X Y : FourTensor) : flatten2 (X-Y)=flatten2 X-flatten2 Y := rfl

@[simp] theorem flatten1_A : flatten1 A = 1 := by
  simp [A,Q0_matrix,Matrix.one_kronecker_one]
@[simp] theorem flatten0_B : flatten0 B = 1 := by
  simp [B,Q0_matrix,Matrix.one_kronecker_one]
@[simp] theorem flatten2_A : flatten2 A = 1 := by
  simp [A,Q0_matrix,Matrix.one_kronecker_one]
@[simp] theorem flatten2_B : flatten2 B = tensorSwap := by
  simp [B,Q0_matrix,Matrix.one_kronecker_one]

/-- The rank-one matching-two test in the matching-zero branch. -/
theorem matching0_second_inverse (U V : Matrix Bool Bool ℂ) (hU : U.det ≠ 0)
    (h : (flatten2 (P0 U V-B)).rank = 1) : V=U⁻¹.transpose := by
  have he : flatten2 (P0 U V-B)*tensorSwap=swapDifference U V 1 := by
    rw [flatten2_sub,flatten2_P0,flatten2_B,Matrix.sub_mul,tensorSwap_sq]
    simp [swapDifference]
  have hr : (swapDifference U V 1).rank=1 := by
    rw [← he,rank_mul_tensorSwap]
    exact h
  simpa using (swap_rank_one_iff U V 1 (isUnit_iff_ne_zero.mpr hU) one_ne_zero).mp hr

/-- The rank-one matching-two test in the matching-one branch. -/
theorem matching1_first_inverse (U V : Matrix Bool Bool ℂ) (hU : U.det ≠ 0)
    (h : (flatten2 (A-P1 U V)).rank = 1) : V=U⁻¹.transpose := by
  have he : flatten2 (A-P1 U V) = -swapDifference U V 1 := by
    rw [flatten2_sub,flatten2_A,flatten2_P1]
    simp [swapDifference]
  rw [he,matrix_rank_neg] at h
  simpa using (swap_rank_one_iff U V 1 (isUnit_iff_ne_zero.mpr hU) one_ne_zero).mp h

/-- The first rank-one test determines the factors in the matching-two branch. -/
theorem matching2_first_inverse (U V : Matrix Bool Bool ℂ) (hU : U.det ≠ 0)
    (h : (flatten1 (A-P2 U V)).rank = 1) : V=U⁻¹.transpose := by
  have he : flatten1 (A-P2 U V) = -swapDifference U V 1 := by
    rw [flatten1_sub,flatten1_A,flatten1_P2]
    simp [swapDifference]
  rw [he,matrix_rank_neg] at h
  simpa using (swap_rank_one_iff U V 1 (isUnit_iff_ne_zero.mpr hU) one_ne_zero).mp h

/-- The other flattening supplies the second transpose-inverse equation. -/
theorem matching2_second_inverse (U V : Matrix Bool Bool ℂ) (hU : U.det ≠ 0)
    (h : (flatten0 (P2 U V-B)).rank = 1) : V.transpose=U⁻¹.transpose := by
  have he : flatten0 (P2 U V-B) = swapDifference U V.transpose 1 := by
    rw [flatten0_sub,flatten0_P2,flatten0_B]
    simp [swapDifference]
  rw [he] at h
  simpa using (swap_rank_one_iff U V.transpose 1 (isUnit_iff_ne_zero.mpr hU) one_ne_zero).mp h

theorem transpose_mul_inverseTranspose (U : Matrix Bool Bool ℂ) (hU : U.det ≠ 0) :
    U.transpose * U⁻¹.transpose = 1 := by
  rw [← Matrix.transpose_mul,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU),
    Matrix.transpose_one]

theorem matching0_bridge_exceptional (U V : Matrix Bool Bool ℂ) (hU : U.det ≠ 0)
    (hA : (flatten0 (A-P0 U V)).rank=1) (hB : (flatten2 (P0 U V-B)).rank=1) :
    P0 U V=A := by
  have hv := matching0_second_inverse U V hU hB
  apply inverse_matching_simple_difference U V
  · rw [hv]; exact transpose_mul_inverseTranspose U hU
  · exact hA.le

theorem matching1_bridge_exceptional (U V : Matrix Bool Bool ℂ) (hU : U.det ≠ 0)
    (hA : (flatten2 (A-P1 U V)).rank=1) (hB : (flatten1 (P1 U V-B)).rank=1) :
    P1 U V=B := by
  have hv := matching1_first_inverse U V hU hA
  have he : flatten0 (A-P0 U V) = -flatten1 (P1 U V-B) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [flatten0,flatten1,A,B,P0,P1,Q0,Holant.Signature.equality]
  have hr : (flatten0 (A-P0 U V)).rank ≤ 1 := by
    rw [he,matrix_rank_neg,hB]
  have h0 : P0 U V=A := inverse_matching_simple_difference U V
    (by rw [hv]; exact transpose_mul_inverseTranspose U hU) hr
  funext x
  have hh := congrFun h0 ![x 0,x 2,x 1,x 3]
  simpa [P0,P1,A,B] using hh

theorem matching2_bridge_symmetric (U V : Matrix Bool Bool ℂ) (hU : U.det ≠ 0)
    (hA : (flatten1 (A-P2 U V)).rank=1) (hB : (flatten0 (P2 U V-B)).rank=1) :
    V=U⁻¹.transpose ∧ U.transpose=U := by
  have hv := matching2_first_inverse U V hU hA
  have hvt := matching2_second_inverse U V hU hB
  refine ⟨hv,?_⟩
  rw [hv,Matrix.transpose_transpose] at hvt
  have hinv := congrArg (fun M : Matrix Bool Bool ℂ => M⁻¹) hvt
  simpa only [← Matrix.transpose_nonsing_inv,
    Matrix.nonsing_inv_nonsing_inv U (isUnit_iff_ne_zero.mpr hU)] using hinv.symm

/-- The parameter-level statement preserves the original first factor, which
allows a concrete group-membership proof to be carried into the bridge form. -/
theorem matching2_scaled_bridge_factors (U V : Matrix Bool Bool ℂ) (hU : U.det≠0)
    (hA : (flatten1 (A-(2:ℂ)•P2 U V)).rank=1)
    (hB : (flatten0 ((2:ℂ)•P2 U V-B)).rank=1) :
    V=(1/2:ℂ)•U⁻¹.transpose ∧ U.transpose=U := by
  have he : (2:ℂ)•P2 U V=P2 U ((2:ℂ)•V) := by
    funext x
    simp [P2,smul_eq_mul]
    ring
  rw [he] at hA hB
  obtain ⟨hv,hu⟩ := matching2_bridge_symmetric U ((2:ℂ)•V) hU hA hB
  refine ⟨?_,hu⟩
  calc V=(1/2:ℂ)•((2:ℂ)•V) := by module
    _=(1/2:ℂ)•U⁻¹.transpose := by rw [hv]

/-- Universal necessity for the full invertible matching cone. All three
membership hypotheses refer to the literal cone, with no conclusion encoded in
the hypotheses and no finite-group assumption. -/
theorem invertible_bridge_necessity (W : FourTensor)
    (hW : InvertibleMatchingCone W) (hA : InvertibleMatchingCone (A-(2:ℂ)•W))
    (hB : InvertibleMatchingCone ((2:ℂ)•W-B)) :
    W=0 ∨ W=(1/2:ℂ)•A ∨ W=(1/2:ℂ)•B ∨
      ∃ U : Matrix Bool Bool ℂ, U.det≠0 ∧ U.transpose=U ∧
        W=(1/2:ℂ)•P2 U U⁻¹.transpose := by
  rcases hW with hW | ⟨r,hr⟩
  · exact Or.inl hW
  rcases hA with hA | ⟨s,hs⟩
  · right; left
    have he := sub_eq_zero.mp hA
    calc W=(1/2:ℂ)•((2:ℂ)•W) := by module
      _=(1/2:ℂ)•A := by rw [← he]
  rcases hB with hB | ⟨t,ht⟩
  · right; right; left
    have he := sub_eq_zero.mp hB
    calc W=(1/2:ℂ)•((2:ℂ)•W) := by module
      _=(1/2:ℂ)•B := by rw [he]
  have hi := invertible_bridge_matching_indices W r s t hr hs ht
  obtain ⟨U,V,hU,hV,he⟩ := hr.smul 2 (by norm_num)
  rcases hi with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have he' : (2:ℂ)•W=P0 U V := by simpa [matchingTensor] using he
    have ha : (flatten0 (A-P0 U V)).rank=1 := by simpa [he',flatten] using hs.rank 0
    have hb : (flatten2 (P0 U V-B)).rank=1 := by simpa [he',flatten] using ht.rank 2
    have hh := matching0_bridge_exceptional U V hU ha hb
    right; left
    calc W=(1/2:ℂ)•((2:ℂ)•W) := by module
      _=(1/2:ℂ)•A := by rw [he',hh]
  · have he' : (2:ℂ)•W=P1 U V := by simpa [matchingTensor] using he
    have ha : (flatten2 (A-P1 U V)).rank=1 := by simpa [he',flatten] using hs.rank 2
    have hb : (flatten1 (P1 U V-B)).rank=1 := by simpa [he',flatten] using ht.rank 1
    have hh := matching1_bridge_exceptional U V hU ha hb
    right; right; left
    calc W=(1/2:ℂ)•((2:ℂ)•W) := by module
      _=(1/2:ℂ)•B := by rw [he',hh]
  · have he' : (2:ℂ)•W=P2 U V := by simpa [matchingTensor] using he
    have ha : (flatten1 (A-P2 U V)).rank=1 := by simpa [he',flatten] using hs.rank 1
    have hb : (flatten0 (P2 U V-B)).rank=1 := by simpa [he',flatten] using ht.rank 0
    obtain ⟨hv,hu⟩ := matching2_bridge_symmetric U V hU ha hb
    right; right; right
    refine ⟨U,hU,hu,?_⟩
    calc W=(1/2:ℂ)•((2:ℂ)•W) := by module
      _=(1/2:ℂ)•P2 U U⁻¹.transpose := by rw [he',hv]

end
end Holant.Certificates.MatchingProductBridge
