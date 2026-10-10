import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch.Arithmetic
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.RelationCode
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.Soundness


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
open Holant.LocalDrafts.EffectiveAlgebraic PowerArithmetic ComplexIsolation
open CommonPrimitive
open scoped BigOperators

structure Data (m n q d : ℕ) where
  relation : Vector d
  certificate : Certificate
  source : RationalBox
  expression : Fin m → RationalPolynomialCode
  multiplier : Fin q → Poly n d
  deriving Encodable

abbrev Candidate (m n q : ℕ) := Σ d : ℕ, Data m n q d

def check {m n : ℕ} (target : Fin m → RootCode) (S : EncodedSystem.System m n)
    (r : Candidate m n S.length) : Bool :=
  decide (r.2.source = RationalBox.ofRectangle r.2.certificate.rectangle) &&
    (r.2.certificate.check (relationCode r.2.relation) &&
      (CommonFieldCheck.checkFamily r.2.relation r.2.source r.2.expression target &&
        zeroCoefficients (defect r.2.relation r.2.expression S r.2.multiplier)))

/-- No minimal-polynomial or irreducibility hypothesis occurs in soundness.
An arbitrary certified root of the proposed relation defines the needed map. -/
theorem check_sound {m n : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (S : EncodedSystem.System m n)
    (r : Candidate m n S.length) (hc : check target S r = true) :
    ¬ ∃ x : Fin n → ℂ, ∀ e ∈ S, MvPolynomial.aeval x (EncodedSystem.polynomial w e) = 0 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hbox, hroot, hfamily, hidentity⟩ := hc
  obtain ⟨θ, hθ⟩ := Certificate.check_sound hroot
  have hr : θ^(r.1+1) = decode θ r.2.relation := by
    apply relation_of_root
    simpa only [RootCode.polynomial, Certificate.rootCode, relationCode_polynomial] using hθ.2.2.1
  have hsource : r.2.source.Contains θ := by
    rw [hbox]
    exact RationalBox.contains_ofRectangle hθ.2.1
  have hw := CommonFieldCheck.checkFamily_sound r.2.relation r.2.source r.2.expression
    target θ w hr hsource ht hfamily
  have hi := zeroCoefficients_sound θ _ hidentity
  rw [value_defect θ r.2.relation hr r.2.expression w hw S r.2.multiplier] at hi
  have hid : (∑ i, value θ (r.2.multiplier i) * equation w (S.get i)) = 1 := sub_eq_zero.mp hi
  rintro ⟨x, hx⟩
  have hz (i : Fin S.length) : MvPolynomial.aeval x (equation w (S.get i)) = 0 := by
    rw [equation_complex]
    exact hx _ (List.get_mem _ _)
  have he := congrArg (MvPolynomial.aeval x) hid
  simpa only [map_sum, map_mul, hz, mul_zero, Finset.sum_const_zero, map_one, zero_ne_one] using he

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
