import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Codec
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Scalars
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open ComplexIsolation.CertificateMachine
open Holant.LocalDrafts.Tractability.AffineMachine
namespace BoxPrimitives
noncomputable section
variable {A : Type} {ea : Encoding A Bool}

def center {f : A → RationalBall} (u : Computes ea ballEncoding f) :
    Computes ea rationalEncoding (fun a => (f a).center) :=
  u.andThen (recode (Wiring.firstComputes rationalEncoding rationalEncoding)
    (fun b : RationalBall => (b.center,b.radius)) (fun _ => rfl) (fun _ => rfl))
def radius {f : A → RationalBall} (u : Computes ea ballEncoding f) :
    Computes ea rationalEncoding (fun a => (f a).radius) :=
  u.andThen (recode (Wiring.secondComputes rationalEncoding rationalEncoding)
    (fun b : RationalBall => (b.center,b.radius)) (fun _ => rfl) (fun _ => rfl))
def ball {f g : A → ℚ} (u : Computes ea rationalEncoding f)
    (v : Computes ea rationalEncoding g) :
    Computes ea ballEncoding (fun a => ⟨f a,g a⟩) :=
  recode (pairComputes u v) id (fun _ => rfl) (fun _ => rfl)
def real {f : A → RationalBox} (u : Computes ea boxEncoding f) :
    Computes ea ballEncoding (fun a => (f a).re) :=
  u.andThen (recode (Wiring.firstComputes ballEncoding ballEncoding)
    (fun b : RationalBox => (b.re,b.im)) (fun _ => rfl) (fun _ => rfl))
def imag {f : A → RationalBox} (u : Computes ea boxEncoding f) :
    Computes ea ballEncoding (fun a => (f a).im) :=
  u.andThen (recode (Wiring.secondComputes ballEncoding ballEncoding)
    (fun b : RationalBox => (b.re,b.im)) (fun _ => rfl) (fun _ => rfl))
def box {f g : A → RationalBall} (u : Computes ea ballEncoding f)
    (v : Computes ea ballEncoding g) :
    Computes ea boxEncoding (fun a => ⟨f a,g a⟩) :=
  recode (pairComputes u v) id (fun _ => rfl) (fun _ => rfl)

def ballAdd {f g : A → RationalBall} (u : Computes ea ballEncoding f)
    (v : Computes ea ballEncoding g) : Computes ea ballEncoding (fun a => (f a).add (g a)) :=
  ball (Scalars.add (center u) (center v)) (Scalars.add (radius u) (radius v))
def ballNeg {f : A → RationalBall} (u : Computes ea ballEncoding f) :
    Computes ea ballEncoding (fun a => (f a).neg) :=
  ball ((center u).andThen Holant.LocalDrafts.TraversalCompletion.RationalLP.Comparison.rationalNegate)
    (radius u)
def ballMul {f g : A → RationalBall} (u : Computes ea ballEncoding f)
    (v : Computes ea ballEncoding g) : Computes ea ballEncoding (fun a => (f a).mul (g a)) :=
  ball (Scalars.mul (center u) (center v))
    (Scalars.add (Scalars.add (Scalars.mul (radius u) (radius v))
      (Scalars.mul ((center u).andThen Scalars.absolute) (radius v)))
      (Scalars.mul ((center v).andThen Scalars.absolute) (radius u)))
def add {f g : A → RationalBox} (u : Computes ea boxEncoding f)
    (v : Computes ea boxEncoding g) : Computes ea boxEncoding (fun a => (f a).add (g a)) :=
  box (ballAdd (real u) (real v)) (ballAdd (imag u) (imag v))
def neg {f : A → RationalBox} (u : Computes ea boxEncoding f) :
    Computes ea boxEncoding (fun a => (f a).neg) := box (ballNeg (real u)) (ballNeg (imag u))
def mul {f g : A → RationalBox} (u : Computes ea boxEncoding f)
    (v : Computes ea boxEncoding g) : Computes ea boxEncoding (fun a => (f a).mul (g a)) :=
  box (ballAdd (ballMul (real u) (real v)) (ballNeg (ballMul (imag u) (imag v))))
    (ballAdd (ballMul (real u) (imag v)) (ballMul (imag u) (real v)))

def point : Computes rationalEncoding boxEncoding RationalBox.point :=
  box (ball (identityComputes rationalEncoding) (constantComputes _ rationalEncoding 0))
    (ball (constantComputes _ rationalEncoding 0) (constantComputes _ rationalEncoding 0))
def multiplication : Computes (pairEncoding boxEncoding boxEncoding) boxEncoding
    (fun p => p.1.mul p.2) :=
  mul (Wiring.firstComputes _ _) (Wiring.secondComputes _ _)
def addition : Computes (pairEncoding boxEncoding boxEncoding) boxEncoding
    (fun p => p.1.add p.2) :=
  add (Wiring.firstComputes _ _) (Wiring.secondComputes _ _)

abbrev containmentEncoding := pairEncoding boxEncoding
  ComplexIsolation.CertificateMachine.rectangleEncoding

/-- Each original endpoint is read from the literal target rectangle. -/
def rectangleField (i : Fin 4) :
    Computes ComplexIsolation.CertificateMachine.rectangleEncoding rationalEncoding
      (fun r => (![r.reLower,r.reUpper,r.imLower,r.imUpper] : Fin 4 → ℚ) i) := by
  let left := Wiring.firstComputes ballWireEncoding ballWireEncoding
  let right := Wiring.secondComputes ballWireEncoding ballWireEncoding
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_
    (fun i => Fin.cases ?_ (fun z => Fin.elim0 z) i) i) i) i
  · exact recode (left.andThen (Wiring.firstComputes _ _))
      ComplexIsolation.CertificateMachine.rectangleWire (fun _ => rfl) (fun _ => rfl)
  · exact recode (left.andThen (Wiring.secondComputes _ _))
      ComplexIsolation.CertificateMachine.rectangleWire (fun _ => rfl) (fun _ => rfl)
  · exact recode (right.andThen (Wiring.firstComputes _ _))
      ComplexIsolation.CertificateMachine.rectangleWire (fun _ => rfl) (fun _ => rfl)
  · exact recode (right.andThen (Wiring.secondComputes _ _))
      ComplexIsolation.CertificateMachine.rectangleWire (fun _ => rfl) (fun _ => rfl)

def inside : Computes containmentEncoding encodingBoolBool (fun p => p.1.inside p.2) := by
  let b := Wiring.firstComputes boxEncoding ComplexIsolation.CertificateMachine.rectangleEncoding
  let r := Wiring.secondComputes boxEncoding ComplexIsolation.CertificateMachine.rectangleEncoding
  let loRe := Scalars.sub (center (real b)) (radius (real b))
  let hiRe := Scalars.add (center (real b)) (radius (real b))
  let loIm := Scalars.sub (center (imag b)) (radius (imag b))
  let hiIm := Scalars.add (center (imag b)) (radius (imag b))
  let a := Scalars.less (r.andThen (rectangleField 0)) loRe
  let b' := Scalars.less hiRe (r.andThen (rectangleField 1))
  let c := Scalars.less (r.andThen (rectangleField 2)) loIm
  let d := Scalars.less hiIm (r.andThen (rectangleField 3))
  exact congrComputes (AccessPrograms.bool Bool.and a
    (AccessPrograms.bool Bool.and b' (AccessPrograms.bool Bool.and c d)))
    (fun p => by
      change (decide (p.2.reLower < p.1.re.center-p.1.re.radius) &&
        (decide (p.1.re.center+p.1.re.radius < p.2.reUpper) &&
          (decide (p.2.imLower < p.1.im.center-p.1.im.radius) &&
            decide (p.1.im.center+p.1.im.radius < p.2.imUpper)))) =
        decide (p.2.reLower < p.1.re.center-p.1.re.radius ∧
          p.1.re.center+p.1.re.radius < p.2.reUpper ∧
          p.2.imLower < p.1.im.center-p.1.im.radius ∧
          p.1.im.center+p.1.im.radius < p.2.imUpper)
      simp only [Bool.decide_and])

theorem multiplication_primitive (p : RationalBox × RationalBox) :
    primitiveCost multiplication.machine (multiplication.outputs p).steps
      (some (Turing.initList multiplication.machine.computer
        ((pairEncoding boxEncoding boxEncoding).encode p))) ≤
      (primitivePolynomial multiplication).eval
        ((pairEncoding boxEncoding boxEncoding).encode p).length :=
  computes_primitive_cost multiplication p

theorem inside_primitive (p : RationalBox × RationalRectangle) :
    primitiveCost inside.machine (inside.outputs p).steps
      (some (Turing.initList inside.machine.computer (containmentEncoding.encode p))) ≤
      (primitivePolynomial inside).eval (containmentEncoding.encode p).length :=
  computes_primitive_cost inside p

end
end BoxPrimitives
end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
