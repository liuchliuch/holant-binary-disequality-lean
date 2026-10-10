import Holant.Certificates.MatchingContractionClosure.SinglePair

namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
variable {K P E : Type*} [Field K] [DecidableEq P] [Fintype E] [DecidableEq E]

theorem nonsingular_has_entry (B : Binary (K := K)) (hB : Matrix.det B≠0) :
    ∃ a b : Bool, B a b≠0 := by
  by_contra hn
  push_neg at hn
  have hz : B=0 := by ext a b; exact hn a b
  exact hB (by simp [hz])

theorem productValue_nonzero (p : (E × Bool) ≃ P) (A : E → Binary (K := K)) (κ : K)
    (hA : ∀ e, Matrix.det (A e)≠0) (hκ : κ≠0) : productValue p A κ≠0 := by
  choose a b hab using fun e => nonsingular_has_entry (A e) (hA e)
  let x : P → Bool := fun i => if (p.symm i).2 then b (p.symm i).1 else a (p.symm i).1
  have hx : productValue p A κ x≠0 := by
    unfold productValue
    apply mul_ne_zero hκ
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    simpa only [x,Equiv.symm_apply_apply,Bool.false_eq_true,ite_true,ite_false] using hab e
  intro hz
  exact hx (congrFun hz x)

theorem spliceFactors_nonsingular (C : Binary (K := K)) (A : E → Binary (K := K))
    (e f : E) (hC : Matrix.det C≠0) (hA : ∀ d, Matrix.det (A d)≠0) :
    ∀ d, Matrix.det (spliceFactors C A e f d)≠0 := by
  intro d
  unfold spliceFactors
  split
  · simp only [fuse,Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (hA e) hC) (hA f)
  · exact hA d.val

theorem contract_cross_nonzero (p : (E × Bool) ≃ P) (A : E → Binary (K := K)) (κ : K)
    (e f : E) (hef : e≠f) (C : Binary (K := K)) (hC : Matrix.det C≠0)
    (hA : ∀ d, Matrix.det (A d)≠0) (hκ : κ≠0) :
    contractPair (p (e,true)) (p (f,false)) C (productValue p A κ)≠0 := by
  rw [contract_cross p A κ e f hef]
  exact productValue_nonzero _ _ _ (spliceFactors_nonsingular C A e f hC hA) hκ

/-- Exactly the closed-cycle trace, and no unrelated matrix nonsingularity
condition, decides whether this same-edge contraction vanishes. -/
theorem contract_matched_zero_iff (p : (E × Bool) ≃ P) (A : E → Binary (K := K)) (κ : K)
    (e : E) (C : Binary (K := K)) (hA : ∀ d, Matrix.det (A d)≠0) (hκ : κ≠0) :
    contractPair (p (e,false)) (p (e,true)) C (productValue p A κ)=0 ↔ trace (A e) C=0 := by
  rw [contract_matched]
  constructor
  · intro hz
    by_contra ht
    exact productValue_nonzero _ _ _ (fun d : OtherEdges e => hA d.val) (mul_ne_zero ht hκ) hz
  · intro ht
    funext x
    simp [productValue,ht]

end
end Holant.Certificates.MatchingContractionClosure
