import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.Candidate
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.RelationCode
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.Certificate


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
open Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open ComplexIsolation PowerArithmetic

theorem certificate_box (t : Certificate) :
    RationalBox.ofRectangle t.rectangle =
      ⟨⟨t.center.1, t.radius⟩, ⟨t.center.2, t.radius⟩⟩ := by
  simp only [RationalBox.ofRectangle, Certificate.rectangle, RationalBall.ofEndpoints]
  congr 2 <;> ring

theorem certificate_small (t : Certificate) {θ : ℂ} {ε : ℝ}
    (ht : t.rectangle.Contains θ) (hε : (t.radius : ℝ) < ε) :
    BoxLimit.Small θ ε (RationalBox.ofRectangle t.rectangle) := by
  rcases ht with ⟨hr₁, hr₂, hi₁, hi₂⟩
  simp only [Certificate.rectangle, Rat.cast_sub, Rat.cast_add] at hr₁ hr₂ hi₁ hi₂
  have hrad : (0 : ℝ) < t.radius := by linarith
  have hre : |(t.center.1 : ℝ) - θ.re| < (t.radius : ℝ) :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  have him : |(t.center.2 : ℝ) - θ.im| < (t.radius : ℝ) :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [certificate_box]
  exact ⟨hre.trans hε, by simpa only [abs_of_pos hrad] using hε,
    him.trans hε, by simpa only [abs_of_pos hrad] using hε⟩

/-- The certificate-completeness call uses this radius threshold verbatim: its
certificate must represent THIS primitive root and have radius below ε.
No certificate-existence field or validation theorem is a premise here. -/
theorem candidate_certificate_radius {m k : ℕ} (w : Fin m → AlgebraicComplex)
    (target : Fin m → RootCode) (ht : ∀ i, (target i).Represents (w i : ℂ))
    (S : EncodedSystem.System m (5 + k)) (y : Fin (5 + k) → AlgebraicComplex)
    (hy : ∀ f ∈ S, MvPolynomial.aeval (fun j => (y j : ℂ))
      (EncodedSystem.polynomial (fun i => (w i : ℂ)) f) = 0)
    (hg : y (Fin.castAdd k 4) *
      (y (Fin.castAdd k 0) * y (Fin.castAdd k 3) -
        y (Fin.castAdd k 1) * y (Fin.castAdd k 2)) = 1) :
    ∃ (θ : ℂ) (d : ℕ) (c : Vector d) (e : Fin m → RationalPolynomialCode)
      (x : MatrixWitness.Candidate d k) (p : RationalPolynomialCode) (ε : ℝ),
      p = relationCode c ∧ p.polynomial = PowerArithmetic.polynomial c ∧
      PowerArithmetic.polynomial c = minpoly ℚ θ ∧
      Polynomial.aeval θ p.polynomial = 0 ∧
      Polynomial.aeval θ p.polynomial.derivative ≠ 0 ∧ 0 < ε ∧
      (∀ i, Polynomial.aeval θ (e i).polynomial = (w i : ℂ)) ∧
      (∀ j, decode θ (x j) = (y j : ℂ)) ∧
      ∀ t : Certificate, t.rectangle.Contains θ → (t.radius : ℝ) < ε →
        MatrixWitness.checkCandidate c (RationalBox.ofRectangle t.rectangle) e target S x = true := by
  obtain ⟨θ, d, c, e, x, ε, _, hmin, hsimple, he, hx, hε, hb⟩ :=
    candidate_small w target ht S y hy hg
  refine ⟨θ, d, c, e, x, relationCode c, ε, rfl, relationCode_polynomial c,
    hmin, ?_, ?_, hε, he, hx, ?_⟩
  · rw [relationCode_polynomial, hmin]; exact minpoly.aeval ℚ θ
  · simpa only [relationCode_polynomial] using hsimple
  · intro t ht hrad
    exact hb _ (certificate_small t ht hrad)

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
