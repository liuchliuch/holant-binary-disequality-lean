import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Codec
import Holant.Proofs.Traversal.RationalLP.Comparison
import Holant.Complexity.FixedFieldMachines.RationalCircuit


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open scoped QuadraticAlgebra
namespace Scalars
open Holant.LocalDrafts.TraversalCompletion.RationalLP

def gadd (a b : Gaussian) : Gaussian := (a.1 + b.1, a.2 + b.2)
def gneg (a : Gaussian) : Gaussian := (-a.1,-a.2)
def gmul (a b : Gaussian) : Gaussian := (a.1*b.1-a.2*b.2, a.1*b.2+a.2*b.1)
def gsize (a : Gaussian) : ℚ := |a.1| + |a.2|
def scalar (q : ℚ) : Gaussian := (q,0)

@[simp] theorem gaussian_gadd (a b : Gaussian) : gaussian (gadd a b) = gaussian a + gaussian b := by
  ext <;> simp [gaussian, gadd]
@[simp] theorem gaussian_gneg (a : Gaussian) : gaussian (gneg a) = -gaussian a := by
  ext <;> simp [gaussian, gneg]
@[simp] theorem gaussian_gmul (a b : Gaussian) : gaussian (gmul a b) = gaussian a * gaussian b := by
  ext <;> simp [gaussian, gmul] <;> ring
@[simp] theorem gaussian_scalar (q : ℚ) : gaussian (scalar q) = (q : GaussianRational) := by
  ext <;> simp [gaussian, scalar]
@[simp] theorem gsize_eq (a : Gaussian) : gsize a = size (gaussian a) := rfl

noncomputable section
variable {A : Type} {ea : Encoding A Bool}

def add {f g : A → ℚ} (u : Computes ea rationalEncoding f) (v : Computes ea rationalEncoding g) :
    Computes ea rationalEncoding (fun a => f a + g a) :=
  (pairComputes u v).andThen RationalArithmetic.additionComputes
def mul {f g : A → ℚ} (u : Computes ea rationalEncoding f) (v : Computes ea rationalEncoding g) :
    Computes ea rationalEncoding (fun a => f a * g a) :=
  (pairComputes u v).andThen RationalArithmetic.multiplicationComputes
def sub {f g : A → ℚ} (u : Computes ea rationalEncoding f) (v : Computes ea rationalEncoding g) :
    Computes ea rationalEncoding (fun a => f a - g a) :=
  (pairComputes u v).andThen Comparison.rationalDifference
def less {f g : A → ℚ} (u : Computes ea rationalEncoding f) (v : Computes ea rationalEncoding g) :
    Computes ea encodingBoolBool (fun a => decide (f a < g a)) :=
  (pairComputes u v).andThen Comparison.rationalLess

def absolute : Computes rationalEncoding rationalEncoding abs :=
  congrComputes (ifComputes Comparison.rationalLessZero Comparison.rationalNegate
    (identityComputes rationalEncoding)) (fun q => by
      by_cases h : q < 0
      · simp [h, abs_of_neg h]
      · simp [h, abs_of_nonneg (le_of_not_gt h)])

def real {f : A → Gaussian} (u : Computes ea gaussianEncoding f) :
    Computes ea rationalEncoding (fun a => (f a).1) :=
  u.andThen (Wiring.firstComputes rationalEncoding rationalEncoding)
def imag {f : A → Gaussian} (u : Computes ea gaussianEncoding f) :
    Computes ea rationalEncoding (fun a => (f a).2) :=
  u.andThen (Wiring.secondComputes rationalEncoding rationalEncoding)

def gaussianAdd {f g : A → Gaussian}
    (u : Computes ea gaussianEncoding f) (v : Computes ea gaussianEncoding g) :
    Computes ea gaussianEncoding (fun a => gadd (f a) (g a)) :=
  pairComputes (add (real u) (real v)) (add (imag u) (imag v))
def gaussianNeg {f : A → Gaussian} (u : Computes ea gaussianEncoding f) :
    Computes ea gaussianEncoding (fun a => gneg (f a)) :=
  pairComputes ((real u).andThen Comparison.rationalNegate)
    ((imag u).andThen Comparison.rationalNegate)
def gaussianMul {f g : A → Gaussian}
    (u : Computes ea gaussianEncoding f) (v : Computes ea gaussianEncoding g) :
    Computes ea gaussianEncoding (fun a => gmul (f a) (g a)) :=
  pairComputes (sub (mul (real u) (real v)) (mul (imag u) (imag v)))
    (add (mul (real u) (imag v)) (mul (imag u) (real v)))
def gaussianSize {f : A → Gaussian} (u : Computes ea gaussianEncoding f) :
    Computes ea rationalEncoding (fun a => gsize (f a)) :=
  add ((real u).andThen absolute) ((imag u).andThen absolute)

def naturalCast : Computes encodingNatBool rationalEncoding (fun n => (n : ℚ)) :=
  congrComputes ((pairComputes RationalArithmetic.natCastComputes
    (constantComputes encodingNatBool encodingNatBool 1)).andThen
      RationalArithmetic.normalizationForwardComputes) (fun n => by
        change mkRat (n : ℤ) 1 = (n : ℚ)
        rw [Rat.mkRat_one]
        simp)

def termDerivative : Computes termEncoding termEncoding (fun t : ℕ × ℚ => (t.1-1,t.2*t.1)) :=
  pairComputes
    ((Wiring.firstComputes encodingNatBool rationalEncoding).andThen
      Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.predComputes)
    (mul (Wiring.secondComputes encodingNatBool rationalEncoding)
      ((Wiring.firstComputes encodingNatBool rationalEncoding).andThen naturalCast))

/-- This traversal consumes and re-emits every physical sparse coefficient
record, including exponent zero and zero coefficients. -/
def derivative : Computes polynomialEncoding polynomialEncoding RealIsolation.derivativeCode := by
  let w := Holant.LocalDrafts.Tractability.AffineMachine.WireLists.mapComputes
    termEncoding termEncoding (fun t : ℕ × ℚ => (t.1-1,t.2*t.1)) termDerivative
  apply congrComputes w
  intro p
  induction p with
  | nil => rfl
  | cons t ps ih =>
    rcases t with ⟨k,q⟩
    simp only [List.map_cons, RealIsolation.derivativeCode, ih]

def secondDerivative : Computes polynomialEncoding polynomialEncoding
    (fun p => RealIsolation.derivativeCode (RealIsolation.derivativeCode p)) := derivative.andThen derivative

theorem derivative_primitive_bound (p : RationalPolynomialCode) :
    primitiveCost derivative.machine (derivative.outputs p).steps
      (some (Turing.initList derivative.machine.computer (polynomialEncoding.encode p))) ≤
        (primitivePolynomial derivative).eval (polynomialEncoding.encode p).length :=
  computes_primitive_cost derivative p

theorem derivative_output_bound (p : RationalPolynomialCode) :
    (polynomialEncoding.encode (RealIsolation.derivativeCode p)).length ≤
      derivative.outputBound.bound.eval (polynomialEncoding.encode p).length :=
  derivative.outputBound.length_le p

end
end Scalars
end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine
