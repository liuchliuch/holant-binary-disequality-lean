import Holant.Proofs.Recognition.TensorDecisionMatching
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# The structural test is invariant under exact coefficient embeddings

An implementation may evaluate the literal original input rows in its effective
coefficient field. An injective field embedding into the source field preserves
all pivot tests, generated factors, and row identities, so it returns exactly the
same Boolean. This theorem assumes only an exact coefficient embedding, never a
recognizer, factorization, correct evaluator, or machine implementation.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionTransport

open TensorDecisionNormalization

variable {K L : Type*} [Field K] [Field L] (φ : K →+* L)
variable (hφ : Function.Injective φ) {n : ℕ}

theorem normalizedSlice_map (f : Signature K n) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool)
    (i : Fin count) (y : Fin (arity i) → Bool) :
    normalizedSlice (fun x => φ (f x)) count arity ports pivot i y =
      φ (normalizedSlice f count arity ports pivot i y) := by
  simp only [normalizedSlice, map_div₀]

theorem candidate_map (f : Signature K n) (S : TensorDecision.Shape n)
    (pivot x : Fin n → Bool) :
    TensorDecision.candidate (fun y => φ (f y)) S pivot x =
      φ (TensorDecision.candidate f S pivot x) := by
  simp only [TensorDecision.candidate, normalizedSlice_map, map_mul, map_prod]

include hφ in
theorem accepts_map_iff (f : Signature K n) (S : TensorDecision.Shape n)
    (pivot : Fin n → Bool) :
    TensorDecision.Accepts (fun x => φ (f x)) S pivot ↔ TensorDecision.Accepts f S pivot := by
  simp only [TensorDecision.Accepts, ne_eq, candidate_map, map_eq_zero_iff φ hφ,
    hφ.eq_iff]

include hφ in
theorem finiteTest_map_iff (f : Signature K n) :
    TensorDecision.FiniteTest (fun x => φ (f x)) ↔ TensorDecision.FiniteTest f := by
  simp only [TensorDecision.FiniteTest, accepts_map_iff φ hφ, map_eq_zero_iff φ hφ]

include hφ in
theorem recognize_map [DecidableEq K] [DecidableEq L] (f : Signature K n) :
    TensorDecision.recognize (fun x => φ (f x)) = TensorDecision.recognize f := by
  apply Bool.eq_iff_iff.mpr
  simp only [TensorDecision.recognize, decide_eq_true_eq]
  exact finiteTest_map_iff φ hφ f

theorem stable_candidate_map (f : Signature K n) (S : TensorDecisionStable.Shape n)
    (pivot x : Fin n → Bool) :
    TensorDecisionStable.candidate (fun y => φ (f y)) S pivot x =
      φ (TensorDecisionStable.candidate f S pivot x) := by
  simp only [TensorDecisionStable.candidate, normalizedSlice_map, map_mul, map_prod]

include hφ in
theorem oneHot_map_iff {m : ℕ} (f : Signature K m) :
    Signature.OneHot (fun x => φ (f x)) ↔ Signature.OneHot f := by
  simp only [Signature.OneHot, map_eq_zero_iff φ hφ]

include hφ in
theorem oneHot_accepts_map_iff (f : Signature K n) (S : TensorDecisionStable.Shape n)
    (pivot : Fin n → Bool) :
    TensorDecisionStable.Accepts (fun _ g => Signature.OneHot g) (fun x => φ (f x)) S pivot ↔
      TensorDecisionStable.Accepts (fun _ g => Signature.OneHot g) f S pivot := by
  simp only [TensorDecisionStable.Accepts, ne_eq, stable_candidate_map, Signature.OneHot,
    normalizedSlice_map, map_eq_zero_iff φ hφ, hφ.eq_iff]

include hφ in
theorem oneHot_finiteTest_map_iff (f : Signature K n) :
    TensorDecisionStable.FiniteTest (fun _ g => Signature.OneHot g) (fun x => φ (f x)) ↔
      TensorDecisionStable.FiniteTest (fun _ g => Signature.OneHot g) f := by
  simp only [TensorDecisionStable.FiniteTest, oneHot_accepts_map_iff φ hφ,
    map_eq_zero_iff φ hφ]

include hφ in
theorem recognizeOneHot_map [DecidableEq K] [DecidableEq L] (f : Signature K n) :
    TensorDecisionMatching.recognizeOneHot (fun x => φ (f x)) =
      TensorDecisionMatching.recognizeOneHot f := by
  apply Bool.eq_iff_iff.mpr
  simp only [TensorDecisionMatching.recognizeOneHot, TensorDecisionStable.recognize,
    decide_eq_true_eq]
  exact oneHot_finiteTest_map_iff φ hφ f

end Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionTransport
