import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.Checker


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
open Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic PowerArithmetic

/-- A common primitive, its simple minimal relation, and a positive tolerance
such that EVERY sufficiently small box passes the actual candidate precheck.
All rational data are proved to exist from the supplied original solution. -/
theorem candidate_small {m k : ℕ} (w : Fin m → AlgebraicComplex)
    (target : Fin m → RootCode) (ht : ∀ i, (target i).Represents (w i : ℂ))
    (S : EncodedSystem.System m (5 + k)) (y : Fin (5 + k) → AlgebraicComplex)
    (hy : ∀ f ∈ S, MvPolynomial.aeval (fun j => (y j : ℂ))
      (EncodedSystem.polynomial (fun i => (w i : ℂ)) f) = 0)
    (hg : y (Fin.castAdd k 4) *
      (y (Fin.castAdd k 0) * y (Fin.castAdd k 3) -
        y (Fin.castAdd k 1) * y (Fin.castAdd k 2)) = 1) :
    ∃ (θ : ℂ) (d : ℕ) (c : Vector d) (e : Fin m → RationalPolynomialCode)
      (x : MatrixWitness.Candidate d k) (ε : ℝ),
      IsAlgebraic ℚ θ ∧ PowerArithmetic.polynomial c = minpoly ℚ θ ∧
      Polynomial.aeval θ (PowerArithmetic.polynomial c).derivative ≠ 0 ∧
      (∀ i, Polynomial.aeval θ (e i).polynomial = (w i : ℂ)) ∧
      (∀ j, decode θ (x j) = (y j : ℂ)) ∧ 0 < ε ∧
      ∀ b : RationalBox, BoxLimit.Small θ ε b →
        MatrixWitness.checkCandidate c b e target S x = true := by
  obtain ⟨θ, d, c, e, x, hθ, hmin, hsep, he, hx⟩ := coefficient_witness_primitive w y
  have hroot : Polynomial.aeval θ (PowerArithmetic.polynomial c) = 0 := by
    rw [hmin]; exact minpoly.aeval ℚ θ
  have hsimple := hsep.aeval_derivative_ne_zero hroot
  obtain ⟨ε, hε, hb⟩ := system_check_small θ c e target
    (fun i => (w i : ℂ)) (fun j => (y j : ℂ)) x S hmin he ht hx hy
  have hgC : (y (Fin.castAdd k 4) : ℂ) *
      ((y (Fin.castAdd k 0) : ℂ) * (y (Fin.castAdd k 3) : ℂ) -
        (y (Fin.castAdd k 1) : ℂ) * (y (Fin.castAdd k 2) : ℂ)) = 1 := by
    exact_mod_cast hg
  have hguard := guard_exact θ c x (fun j => (y j : ℂ)) hmin hx hgC
  refine ⟨θ, d, c, e, x, ε, hθ, hmin, hsimple, he, hx, hε, ?_⟩
  intro b hs
  simp only [MatrixWitness.checkCandidate,Bool.and_eq_true_eq_eq_true_and_eq_true]
  exact ⟨hb b hs,hguard⟩

/-- Actual finite data occur in the existing variable-degree fair queue.
This theorem deliberately says `precheckRaw`, not root-validated acceptance. -/
theorem exists_raw_precheck {m k : ℕ} (w : Fin m → AlgebraicComplex)
    (target : Fin m → RootCode) (ht : ∀ i, (target i).Represents (w i : ℂ))
    (S : EncodedSystem.System m (5 + k)) (y : Fin (5 + k) → AlgebraicComplex)
    (hy : ∀ f ∈ S, MvPolynomial.aeval (fun j => (y j : ℂ))
      (EncodedSystem.polynomial (fun i => (w i : ℂ)) f) = 0)
    (hg : y (Fin.castAdd k 4) *
      (y (Fin.castAdd k 0) * y (Fin.castAdd k 3) -
        y (Fin.castAdd k 1) * y (Fin.castAdd k 2)) = 1) :
    ∃ (θ : ℂ) (r : MatrixWitness.RawCandidate m k) (height : ℕ),
      r ∈ MatrixWitness.rawThrough m k height ∧
      MatrixWitness.precheckRaw target S r = true ∧
      PowerArithmetic.polynomial r.2.1 = minpoly ℚ θ ∧
      Polynomial.aeval θ (PowerArithmetic.polynomial r.2.1).derivative ≠ 0 ∧
      r.2.2.1.Contains θ ∧
      (∀ i, decode θ (CommonFieldCheck.familyCoordinates r.2.1 r.2.2.2.1 i) = (w i : ℂ)) ∧
      (∀ j, decode θ (r.2.2.2.2 j) = (y j : ℂ)) := by
  obtain ⟨θ, d, c, e, x, ε, hθ, hmin, hsimple, he, hx, hε, hb⟩ :=
    candidate_small w target ht S y hy hg
  obtain ⟨b, hcontains, hsmall⟩ := BoxLimit.exists_small_box θ ε hε
  let r : MatrixWitness.RawCandidate m k := ⟨d, c, b, e, x⟩
  have hr := relation_of_root θ c (by rw [hmin]; exact minpoly.aeval ℚ θ)
  refine ⟨θ, r, Encodable.encode (fun _ : Fin 1 => r), MatrixWitness.rawThrough_complete r,
    hb b hsmall, hmin, hsimple, hcontains, ?_, hx⟩
  intro i
  change decode θ (CommonFieldCheck.reduce c (e i)) = (w i : ℂ)
  rw [CommonFieldCheck.decode_reduce θ c hr, he]

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
