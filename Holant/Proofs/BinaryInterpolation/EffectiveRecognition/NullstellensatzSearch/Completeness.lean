import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Check
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Coordinates
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.Certified


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
open Holant.Tractable Holant.LocalDrafts.EffectiveAlgebraic PowerArithmetic ComplexIsolation
open CommonPrimitive
variable {m n : ℕ}

theorem exists_checked (w : Fin m → AlgebraicComplex) (target : Fin m → RootCode)
    (ht : ∀ j, (target j).Represents (w j : ℂ)) (S : EncodedSystem.System m n)
    (hn : NoAlgebraicSolution w S) :
    ∃ r : Candidate m n S.length, check target S r = true := by
  obtain ⟨θ, d, c, e, P, hθ, hmin, hsep, he, hzero⟩ := identity_coordinates w S hn
  obtain ⟨ε, hε, hb⟩ := family_check_small θ c e target (fun j => (w j : ℂ)) hmin he ht
  have hroot : Polynomial.aeval θ (relationCode c).polynomial = 0 := by
    rw [relationCode_polynomial, hmin]
    exact minpoly.aeval ℚ θ
  have hsimple : Polynomial.aeval θ (relationCode c).polynomial.derivative ≠ 0 := by
    have hs : (relationCode c).polynomial.Separable := by
      rw [relationCode_polynomial]
      exact hsep
    exact hs.aeval_derivative_ne_zero hroot
  obtain ⟨t, htcheck, hrep, hsmall⟩ := exists_certificate (relationCode c) θ hroot hsimple
    (show 0 < ε / 2 by linarith)
  have hrad : (t.radius : ℝ) < ε := by
    have hpos := ((Certificate.check_iff (relationCode c) t).mp htcheck).1
    have h := radius_lt_of_rectangle_small t hpos hsmall
    linarith
  have hfamily := hb (RationalBox.ofRectangle t.rectangle) (certificate_small t hrep.2.1 hrad)
  let r : Candidate m n S.length := ⟨d, ⟨c, t, RationalBox.ofRectangle t.rectangle, e, P⟩⟩
  refine ⟨r, ?_⟩
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨rfl,htcheck,hfamily,hzero⟩

/-- Explicit change of witness domain, through the original coefficient map. -/
theorem exists_checked_of_noComplex (w : Fin m → AlgebraicComplex) (target : Fin m → RootCode)
    (ht : ∀ j, (target j).Represents (w j : ℂ)) (S : EncodedSystem.System m n)
    (hn : ¬ ∃ x : Fin n → ℂ, ∀ e ∈ S,
      MvPolynomial.aeval x (EncodedSystem.polynomial (fun j => (w j : ℂ)) e) = 0) :
    ∃ r : Candidate m n S.length, check target S r = true :=
  exists_checked w target ht S (noAlgebraic_of_noComplex w S hn)

theorem checked_iff_noComplex (w : Fin m → AlgebraicComplex) (target : Fin m → RootCode)
    (ht : ∀ j, (target j).Represents (w j : ℂ)) (S : EncodedSystem.System m n) :
    (∃ r : Candidate m n S.length, check target S r = true) ↔
      ¬ ∃ x : Fin n → ℂ, ∀ e ∈ S,
        MvPolynomial.aeval x (EncodedSystem.polynomial (fun j => (w j : ℂ)) e) = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    exact check_sound target (fun j => (w j : ℂ)) ht S r hr
  · exact exists_checked_of_noComplex w target ht S

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
