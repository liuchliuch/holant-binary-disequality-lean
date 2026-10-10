import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Evaluation


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Scalars

def absoluteCoefficients (p : RationalPolynomialCode) : RationalPolynomialCode :=
  p.map (fun t => (t.1, |t.2|))
def curvatureValue (p : RationalPolynomialCode) (B : ℚ) : ℚ :=
  (Evaluation.evaluate (absoluteCoefficients (RealIsolation.derivativeCode
    (RealIsolation.derivativeCode p)), scalar B)).1

theorem eval_absoluteCoefficients (p : RationalPolynomialCode) (B : ℚ) :
    evalGaussian (B : GaussianRational) (absoluteCoefficients p) =
      (majorant B p : GaussianRational) := by
  induction p with
  | nil => simp [absoluteCoefficients, evalGaussian, majorant]
  | cons t ps ih =>
    rcases t with ⟨k,q⟩
    simp only [absoluteCoefficients, List.map_cons, evalGaussian, majorant,
      Rat.cast_add, Rat.cast_mul, Rat.cast_pow] at *
    rw [ih]

theorem curvatureValue_eq (p : RationalPolynomialCode) (B : ℚ) : curvatureValue p B = curvature p B := by
  have h := Evaluation.evaluate_correct
    (absoluteCoefficients (RealIsolation.derivativeCode (RealIsolation.derivativeCode p)), scalar B)
  rw [gaussian_scalar, eval_absoluteCoefficients] at h
  have hr := congrArg QuadraticAlgebra.re h
  simpa [gaussian, curvatureValue, curvature] using hr

abbrev Summary := Certificate × (Gaussian × (Gaussian × ℚ))
abbrev summaryTailEncoding := pairEncoding gaussianEncoding (pairEncoding gaussianEncoding rationalEncoding)
abbrev summaryEncoding := pairEncoding certificateEncoding summaryTailEncoding

def prepare (x : Input) : Summary :=
  (x.2, Evaluation.evaluate (x.1,x.2.center),
    Evaluation.evaluate (RealIsolation.derivativeCode x.1,x.2.center), curvatureValue x.1 x.2.magnitude)
def finish (s : Summary) : Bool :=
  decide (0 < s.1.radius ∧ gsize s.1.center + 2*s.1.radius < s.1.magnitude ∧
    gsize (gadd (scalar 1) (gneg (gmul s.1.inverseSlope s.2.2.1))) +
      gsize s.1.inverseSlope * s.2.2.2 * (2*s.1.radius) < 1/2 ∧
    gsize (gmul s.1.inverseSlope s.2.1) < s.1.radius/4)
def check (x : Input) : Bool := finish (prepare x)

theorem check_eq (x : Input) : check x = x.2.check x.1 := by
  have hp := Evaluation.evaluate_correct (x.1,x.2.center)
  have hd := Evaluation.evaluate_correct (RealIsolation.derivativeCode x.1,x.2.center)
  simp only [check, finish, prepare, Certificate.check, Certificate.slopeError,
    Certificate.residual, gsize_eq, gaussian_gadd, gaussian_gneg, gaussian_gmul,
    gaussian_scalar, Rat.cast_one, hp, hd, curvatureValue_eq, sub_eq_add_neg]

noncomputable section
def centerComputes : Computes certificateEncoding gaussianEncoding Certificate.center :=
  recode (Wiring.firstComputes gaussianEncoding
    (pairEncoding gaussianEncoding (pairEncoding rationalEncoding rationalEncoding)))
    certificateWire (fun _ => rfl) (fun _ => rfl)
def certificateRest : Computes certificateEncoding
    (pairEncoding gaussianEncoding (pairEncoding rationalEncoding rationalEncoding))
    (fun t => (t.inverseSlope,t.radius,t.magnitude)) :=
  recode (Wiring.secondComputes gaussianEncoding
    (pairEncoding gaussianEncoding (pairEncoding rationalEncoding rationalEncoding)))
    certificateWire (fun _ => rfl) (fun _ => rfl)
def slopeComputes : Computes certificateEncoding gaussianEncoding Certificate.inverseSlope :=
  certificateRest.andThen (Wiring.firstComputes _ _)
def radiusMagnitude : Computes certificateEncoding (pairEncoding rationalEncoding rationalEncoding)
    (fun t => (t.radius,t.magnitude)) := certificateRest.andThen (Wiring.secondComputes _ _)
def radiusComputes : Computes certificateEncoding rationalEncoding Certificate.radius :=
  radiusMagnitude.andThen (Wiring.firstComputes _ _)
def magnitudeComputes : Computes certificateEncoding rationalEncoding Certificate.magnitude :=
  radiusMagnitude.andThen (Wiring.secondComputes _ _)

def absoluteCoefficientComputes : Computes termEncoding termEncoding (fun t : ℕ × ℚ => (t.1,|t.2|)) :=
  pairComputes (Wiring.firstComputes _ _) ((Wiring.secondComputes _ _).andThen Scalars.absolute)
def absoluteCoefficientsComputes : Computes polynomialEncoding polynomialEncoding absoluteCoefficients :=
  WireLists.mapComputes termEncoding termEncoding _ absoluteCoefficientComputes

def inputPolynomial : Computes inputEncoding polynomialEncoding Prod.fst := Wiring.firstComputes _ _
def inputCertificate : Computes inputEncoding certificateEncoding Prod.snd := Wiring.secondComputes _ _
def inputCenter : Computes inputEncoding gaussianEncoding (fun x => x.2.center) :=
  inputCertificate.andThen centerComputes
def inputMagnitude : Computes inputEncoding rationalEncoding (fun x => x.2.magnitude) :=
  inputCertificate.andThen magnitudeComputes

def evaluationComputes : FiniteComputes inputEncoding gaussianEncoding
    (fun x => Evaluation.evaluate (x.1,x.2.center)) :=
  (FiniteComputes.ofPoly (pairComputes inputPolynomial inputCenter)).andThen Evaluation.computes
def derivativeEvaluationComputes : FiniteComputes inputEncoding gaussianEncoding
    (fun x => Evaluation.evaluate (RealIsolation.derivativeCode x.1,x.2.center)) :=
  (FiniteComputes.ofPoly (pairComputes (inputPolynomial.andThen Scalars.derivative) inputCenter)).andThen
    Evaluation.computes
def curvatureComputes : FiniteComputes inputEncoding rationalEncoding
    (fun x => curvatureValue x.1 x.2.magnitude) :=
  ((FiniteComputes.ofPoly (pairComputes
    ((inputPolynomial.andThen Scalars.secondDerivative).andThen absoluteCoefficientsComputes)
    (pairComputes inputMagnitude (constantComputes inputEncoding rationalEncoding 0)))).andThen
      Evaluation.computes).andThen (FiniteComputes.ofPoly (Wiring.firstComputes _ _))

def prepareComputes : FiniteComputes inputEncoding summaryEncoding prepare :=
  (FiniteComputes.ofPoly inputCertificate).pair
    (evaluationComputes.pair (derivativeEvaluationComputes.pair curvatureComputes))

def finishComputes : Computes summaryEncoding encodingBoolBool finish := by
  let cert := Wiring.firstComputes certificateEncoding summaryTailEncoding
  let vals := Wiring.secondComputes certificateEncoding summaryTailEncoding
  let eval := vals.andThen (Wiring.firstComputes _ _)
  let derivH := vals.andThen (Wiring.secondComputes _ _)
  let deriv := derivH.andThen (Wiring.firstComputes _ _)
  let H := derivH.andThen (Wiring.secondComputes _ _)
  let c := cert.andThen centerComputes
  let b := cert.andThen slopeComputes
  let r := cert.andThen radiusComputes
  let B := cert.andThen magnitudeComputes
  let constant := fun q : ℚ => constantComputes summaryEncoding rationalEncoding q
  let twoR := Scalars.mul (constant 2) r
  let error := gaussianSize (gaussianAdd
    (constantComputes summaryEncoding gaussianEncoding (scalar 1))
    (gaussianNeg (gaussianMul b deriv)))
  let L := Scalars.add error (Scalars.mul (Scalars.mul (gaussianSize b) H) twoR)
  let residual := gaussianSize (gaussianMul b eval)
  let h₁ := Scalars.less (constant 0) r
  let h₂ := Scalars.less (Scalars.add (gaussianSize c) twoR) B
  let h₃ := Scalars.less L (constant (1/2))
  let h₄ := Scalars.less residual (Scalars.mul r (constant (1/4)))
  exact congrComputes (AccessPrograms.bool Bool.and h₁
    (AccessPrograms.bool Bool.and h₂ (AccessPrograms.bool Bool.and h₃ h₄)))
    (fun s => by
      apply Bool.eq_iff_iff.mpr
      simp only [finish, Bool.and_eq_true, decide_eq_true_eq, Function.comp_apply,
        div_eq_mul_inv, one_mul])

/-- Full encoded checker, with a proved finite (not claimed polynomial) bound. -/
def computes : FiniteComputes inputEncoding encodingBoolBool (fun x : Input => x.2.check x.1) :=
  (prepareComputes.andThen (FiniteComputes.ofPoly finishComputes)).congr check_eq

end
end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine
