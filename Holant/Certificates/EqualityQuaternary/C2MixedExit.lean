import Holant.Certificates.EqualityQuaternary.C2Matching

/-! Endpoint-nondegenerate, nonmatching selection among the three actual
mixed-table gadgets. The y=0 rank-one exception is excluded by original
physical tensor primality. No candidate-matching witness is assumed.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2.Mixed
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicQuaternary
open Holant.Projective.CyclicQuaternary.Physical hiding Scalar Mat
open Holant.Marked.SupportAtlas (parity)
open Holant.EightVertex.ProductAnchor (EndpointEven)
set_option backward.isDefEq.respectTransparency false

def twoBlocks (d A B : Scalar) : Signature Scalar 4 :=
  ofCoordinates d d ![(0,0),(A,A),(B,B)]

theorem empty_blocks_interior (d : Scalar) (w : Word)
    (h0 : w≠(fun _ => false)) (h1 : w≠(fun _ => true)) : twoBlocks d 0 0 w=0 := by
  cases h00 : w 0 <;> cases h01 : w 1 <;> cases h02 : w 2 <;> cases h03 : w 3 <;>
    simp [twoBlocks,ofCoordinates,h00,h01,h02,h03]
  · exact False.elim (h0 (by funext i; fin_cases i <;> assumption))
  · exact False.elim (h1 (by funext i; fin_cases i <;> assumption))

theorem matching_single_row {q : Signature Scalar 4} (d A : Scalar)
    (he : walsh q=(4 : Scalar) • twoBlocks d A 0) (h : GroupMatching group q) :
    ∃ sigma : Scalar, (sigma=1 ∨ sigma = -1) ∧ A=sigma*d := by
  have hA : A≠0 := by
    intro hA
    obtain ⟨w,h0,h1,hw⟩ := matching_walsh_interior h
    apply hw
    rw [he,hA]
    change 4*twoBlocks d 0 0 w=0
    rw [empty_blocks_interior d w h0 h1,mul_zero]
  have hn : walsh q (firstWord 1)≠0 := by
    rw [he]
    simpa [twoBlocks,firstWord,join,ofCoordinates] using mul_ne_zero (by norm_num : (4:Scalar)≠0) hA
  have hs := (matching_walsh_square h (firstWord 1)).resolve_left hn
  rw [he] at hs
  have hsq : A^2=d^2 := by
    simp only [Pi.smul_apply,smul_eq_mul,twoBlocks,firstWord,join,endpoint0,ofCoordinates] at hs
    norm_num at hs
    linear_combination hs/16
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hh | hh
  · exact ⟨1,Or.inl rfl,by simpa using hh⟩
  · exact ⟨-1,Or.inr rfl,by simpa using hh⟩

theorem matching_double_row {q : Signature Scalar 4} (d A B : Scalar)
    (he : walsh q=(4 : Scalar) • twoBlocks d A B) (hA : A≠0) (hB : B≠0) :
    ¬GroupMatching group q := by
  intro h
  have hi : (coordinates (walsh q) 1).1≠0 := by
    rw [he]
    simpa [twoBlocks,coordinates,join,ofCoordinates] using mul_ne_zero (by norm_num : (4:Scalar)≠0) hA
  have hj : (coordinates (walsh q) 2).1≠0 := by
    rw [he]
    simpa [twoBlocks,coordinates,join,ofCoordinates] using mul_ne_zero (by norm_num : (4:Scalar)≠0) hB
  have hh := matching_one_block h 1 2 hi hj
  contradiction

theorem output_even (q : Signature Scalar 4) (x y z : Scalar)
    (h : walsh q=mixedTable x y z) (p : Fin 3) :
    ∀ w, Holant.weight w % 2=1 → output q p w=0 := by
  have ht := physical_mixed_table q x y z h p
  have he : EvenSupported (walsh (output q p)) := by
    intro w hw
    rw [ht]
    change 4*row p x y z w=0
    have hr : EvenSupported (row p x y z) := by
      fin_cases p <;> exact ofCoordinates_even _ _ _
    rw [hr w hw,mul_zero]
  have hv : endpoint1 (walsh (output q p))=sign false*endpoint0 (walsh (output q p)) := by
    rw [ht]
    fin_cases p <;> simp [endpoint0,endpoint1,row,ofCoordinates,sign]
  have hc : ∀ i, (coordinates (walsh (output q p)) i).2=
      sign false*(coordinates (walsh (output q p)) i).1 := by
    intro i
    rw [ht]
    fin_cases p <;> fin_cases i <;> simp [coordinates,join,row,ofCoordinates,sign]
  have hf := common_form (output q p) he false hv hc
  intro w hw
  rw [hf]
  exact inverseCommon_parity false _ _ w (by rw [(parity_weight w).mpr hw]; decide)

def endpointValue (p : Fin 3) (x y z : Scalar) : Scalar :=
  8*(x^2+y^2+z^2+(if p=2 then 2*x*y else 0))

theorem output_endpoints (q : Signature Scalar 4) (x y z : Scalar)
    (h : walsh q=mixedTable x y z) (p : Fin 3) :
    output q p (fun _ => false)=endpointValue p x y z ∧
      output q p (fun _ => true)=endpointValue p x y z := by
  have hinv : Signature.coordinateAction (fun _ => P) (walsh (output q p))=output q p :=
    Signature.coordinateAction_cancel _ _ (fun _ => P_Pinv) _
  rw [physical_mixed_table q x y z h p] at hinv
  rw [←hinv]
  constructor <;> fin_cases p <;>
    simp [Signature.coordinateAction,sum_words4,Fin.prod_univ_succ,P,row,ofCoordinates,endpointValue] <;> ring

theorem first_two_obstruction (x y z sigma tau : Scalar) (hz : z≠0)
    (hs : x^2+y^2+z^2≠0) (hsigma : sigma=1 ∨ sigma = -1) (htau : tau=1 ∨ tau = -1)
    (h1 : y^2+z^2=sigma*x^2) (h2 : x^2+z^2=tau*y^2) : False := by
  rcases hsigma with rfl | rfl <;> rcases htau with rfl | rfl
  · have hh : z^2=0 := by linear_combination (h1+h2)/2
    exact hz (sq_eq_zero_iff.mp hh)
  · apply hs; linear_combination h2
  · apply hs; linear_combination h1
  · apply hs; linear_combination h1

/-- For a normalized mixed source, one of the literal three contractions
already has nonzero physical endpoints and is not a C2 matching tensor. -/
theorem normalized_mixed_exit (q : Signature Scalar 4) (x y z : Scalar)
    (hp : TensorPrime q) (hx : x≠0) (hz : z≠0) (h : walsh q=mixedTable x y z) :
    ∃ p : Fin 3, EndpointEven (output q p) ∧ ¬GroupMatching group (output q p) := by
  have endpoints (p : Fin 3) (hn : endpointValue p x y z≠0) : EndpointEven (output q p) :=
    ⟨by rwa [(output_endpoints q x y z h p).1],
      by rwa [(output_endpoints q x y z h p).2],output_even q x y z h p⟩
  by_cases hy : y=0
  · subst y
    have hs := prime_mixed_nonzero_sum q x z hp hx h
    refine ⟨1,endpoints 1 (by simpa [endpointValue] using mul_ne_zero (by norm_num : (8:Scalar)≠0) hs),?_⟩
    intro hm
    apply matching_walsh_endpoint hm
    rw [physical_mixed_table q x 0 z h 1]
    simp [endpoint0,row,ofCoordinates]
  · by_cases hs : x^2+y^2+z^2=0
    · have hA : x^2+y^2≠0 := by
        intro hA
        have hz2 : z^2=0 := by linear_combination hs-hA
        exact hz (sq_eq_zero_iff.mp hz2)
      have hB : 2*x*y≠0 := mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
      refine ⟨2,endpoints 2 ?_,matching_double_row _ _ _ (physical_mixed_table q x y z h 2) hA hB⟩
      simpa [endpointValue,hs] using mul_ne_zero (by norm_num : (8:Scalar)≠0) hB
    · have he0 := endpoints 0 (by simpa [endpointValue] using mul_ne_zero (by norm_num : (8:Scalar)≠0) hs)
      have he1 := endpoints 1 (by simpa [endpointValue] using mul_ne_zero (by norm_num : (8:Scalar)≠0) hs)
      by_cases hm0 : GroupMatching group (output q 0)
      · refine ⟨1,he1,?_⟩
        intro hm1
        obtain ⟨sigma,hsigma,h1⟩ := matching_single_row _ _ (physical_mixed_table q x y z h 0) hm0
        obtain ⟨tau,htau,h2⟩ := matching_single_row _ _ (physical_mixed_table q x y z h 1) hm1
        exact first_two_obstruction x y z sigma tau hz hs hsigma htau h1 h2
      · exact ⟨0,he0,hm0⟩

end Holant.Certificates.EqualityQuaternary.C2.Mixed
