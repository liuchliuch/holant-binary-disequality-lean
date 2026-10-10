import Holant.Certificates.MatchingProductBridge.Flattenings

namespace Holant.Certificates.MatchingProductBridge
open Matrix
noncomputable section

/-- The simple-tensor sum criterion with the identity vector as one factor.
This follows from actual rank-one minors, without a decomposition hypothesis. -/
theorem identity_outer_sub_rank_le_one (U V : Matrix Bool Bool ℂ)
    (h : (vecMulVec (fun i : Bool × Bool => (1 : Matrix Bool Bool ℂ) i.1 i.2)
      (fun j : Bool × Bool => (1 : Matrix Bool Bool ℂ) j.1 j.2) -
      vecMulVec (fun i : Bool × Bool => U i.1 i.2)
      (fun j : Bool × Bool => V j.1 j.2)).rank ≤ 1) :
    (∃ c : ℂ, U = c • 1) ∨ (∃ c : ℂ, V = c • 1) := by
  let e : Bool × Bool → ℂ := fun i => (1 : Matrix Bool Bool ℂ) i.1 i.2
  have hm (i j : Bool × Bool) := minor_two_eq_zero_of_rank_le_one _ h
    (false,false) i (false,false) j
  have hp (i j : Bool × Bool) :
      (U i.1 i.2 - U false false * e i) * (V j.1 j.2 - V false false * e j) = 0 := by
    have hh := hm i j
    simp only [Matrix.sub_apply,vecMulVec,Matrix.of_apply,Prod.fst,Prod.snd,
      Matrix.one_apply_eq,one_mul,mul_one] at hh
    change (1-U false false*V false false)*(e i*e j-U i.1 i.2*V j.1 j.2)-
      (e j-U false false*V j.1 j.2)*(e i-U i.1 i.2*V false false)=0 at hh
    linear_combination -hh
  by_cases hu : ∀ i : Bool × Bool, U i.1 i.2 - U false false * e i = 0
  · left
    refine ⟨U false false,?_⟩
    ext a b
    exact sub_eq_zero.mp (hu (a,b))
  · right
    push_neg at hu
    obtain ⟨i,hi⟩ := hu
    refine ⟨V false false,?_⟩
    ext a b
    exact sub_eq_zero.mp ((mul_eq_zero.mp (hp i (a,b))).resolve_left hi)

/-- If either factor is scalar and the two transpose factors are inverses,
the matching product is exactly the equality product. -/
theorem scalar_inverse_matching_zero (U V : Matrix Bool Bool ℂ)
    (hUV : U.transpose * V = 1)
    (hs : (∃ c : ℂ, U = c • 1) ∨ (∃ c : ℂ, V = c • 1)) :
    P0 U V = A := by
  rcases hs with ⟨c,rfl⟩ | ⟨c,rfl⟩
  · have hcv : c • V = 1 := by simpa using hUV
    funext x
    have hv := congrFun (congrFun hcv (x 2)) (x 3)
    simp only [Matrix.smul_apply,smul_eq_mul] at hv
    change (c * (1 : Matrix Bool Bool ℂ) (x 0) (x 1)) * V (x 2) (x 3) = _
    rw [mul_comm c, mul_assoc, hv]
    simp [A,P0,Q0,Holant.Signature.equality,Matrix.one_apply]
  · have hcu : c • U.transpose = 1 := by simpa using hUV
    have hcu' : c • U = 1 := by
      have ht := congrArg Matrix.transpose hcu
      simpa using ht
    funext x
    have hu := congrFun (congrFun hcu' (x 0)) (x 1)
    simp only [Matrix.smul_apply,smul_eq_mul] at hu
    change U (x 0) (x 1) * (c * (1 : Matrix Bool Bool ℂ) (x 2) (x 3)) = _
    rw [← mul_assoc, mul_comm (U (x 0) (x 1)) c, hu]
    simp [A,P0,Q0,Holant.Signature.equality,Matrix.one_apply]

/-- A simple difference from the equality product can only be exceptional when
its two invertible factors satisfy the transpose-inverse relation. -/
theorem inverse_matching_simple_difference (U V : Matrix Bool Bool ℂ)
    (hUV : U.transpose * V = 1) (h : (flatten0 (A-P0 U V)).rank ≤ 1) :
    P0 U V = A := by
  apply scalar_inverse_matching_zero U V hUV
  apply identity_outer_sub_rank_le_one U V
  have he : vecMulVec (fun i : Bool × Bool => (1 : Matrix Bool Bool ℂ) i.1 i.2)
      (fun j : Bool × Bool => (1 : Matrix Bool Bool ℂ) j.1 j.2) -
      vecMulVec (fun i : Bool × Bool => U i.1 i.2)
      (fun j : Bool × Bool => V j.1 j.2) = flatten0 (A-P0 U V) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [flatten0,A,P0,Q0,Holant.Signature.equality,vecMulVec,Matrix.one_apply]
  rw [he]
  exact h

end
end Holant.Certificates.MatchingProductBridge
