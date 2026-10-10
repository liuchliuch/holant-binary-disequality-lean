import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Multiplication


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open ComplexIsolation.CertificateMachine (termEncoding polynomialEncoding)
open Holant.LocalDrafts.Tractability.AffineMachine

namespace Coordinates
theorem sum_cons (n : ℕ) (v : List ℚ) (vs : List (List ℚ)) :
    sum n (v::vs) = add n v (sum n vs) := by
  simp only [sum, add, tab_ofFn, List.map_cons, List.sum_cons, at_ofFn]

theorem reduce_sum (c : List ℚ) (p : RationalPolynomialCode) :
    sum c.length (p.map (fun t => scale t.2 (power c t.1))) = reduce c p := by
  induction p with
  | nil => simp [sum, reduce, zero]
  | cons t ps ih =>
    rcases t with ⟨k,q⟩
    rw [List.map_cons,sum_cons,ih]
    rfl

theorem evalAt_sum (c v : List ℚ) (p : RationalPolynomialCode) :
    sum c.length (p.map (fun t => scale t.2 (powerAt c v t.1))) = evalAt c v p := by
  induction p with
  | nil => simp [sum, evalAt, zero]
  | cons t ps ih =>
    rcases t with ⟨k,q⟩
    rw [List.map_cons,sum_cons,ih]
    rfl
end Coordinates

namespace PolynomialEvaluation
abbrev reduceEncoding := pairEncoding coordinatesEncoding polynomialEncoding
abbrev evalEncoding := pairEncoding Companion.shiftEncoding polynomialEncoding

noncomputable def reduceCell : Executes (pairEncoding coordinatesEncoding termEncoding)
    coordinatesEncoding (fun p => Coordinates.scale p.2.2 (Coordinates.power p.1 p.2.1)) := by
  let c := Wiring.firstComputes coordinatesEncoding termEncoding
  let t := Wiring.secondComputes coordinatesEncoding termEncoding
  let k := t.andThen (Wiring.firstComputes encodingNatBool rationalEncoding)
  let q := t.andThen (Wiring.secondComputes encodingNatBool rationalEncoding)
  let power := (Executes.ofComputes (pairComputes c k)).comp Companion.power
  exact (Executes.pair (Executes.ofComputes q) power).comp
    (Executes.ofComputes CoordinatePrimitives.scale)

noncomputable def reduce : Executes reduceEncoding coordinatesEncoding
    (fun p => Coordinates.reduce p.1 p.2) := by
  let terms := Executes.mapList coordinatesEncoding termEncoding coordinatesEncoding
    (fun c t => Coordinates.scale t.2 (Coordinates.power c t.1)) reduceCell
  let n := (Wiring.firstComputes coordinatesEncoding polynomialEncoding).andThen
    (WireLists.lengthComputes rationalEncoding)
  exact Executes.congr ((Executes.pair (Executes.ofComputes n) terms).comp Companion.sum)
    (fun p => Coordinates.reduce_sum p.1 p.2)

noncomputable def evalCell : Executes (pairEncoding Companion.shiftEncoding termEncoding)
    coordinatesEncoding (fun p => Coordinates.scale p.2.2
      (Coordinates.powerAt p.1.1 p.1.2 p.2.1)) := by
  let cv := Wiring.firstComputes Companion.shiftEncoding termEncoding
  let t := Wiring.secondComputes Companion.shiftEncoding termEncoding
  let k := t.andThen (Wiring.firstComputes encodingNatBool rationalEncoding)
  let q := t.andThen (Wiring.secondComputes encodingNatBool rationalEncoding)
  let power := (Executes.ofComputes (pairComputes cv k)).comp Multiplication.powerAt
  exact (Executes.pair (Executes.ofComputes q) power).comp
    (Executes.ofComputes CoordinatePrimitives.scale)

noncomputable def evalAt : Executes evalEncoding coordinatesEncoding
    (fun p => Coordinates.evalAt p.1.1 p.1.2 p.2) := by
  let terms := Executes.mapList Companion.shiftEncoding termEncoding coordinatesEncoding
    (fun cv t => Coordinates.scale t.2 (Coordinates.powerAt cv.1 cv.2 t.1)) evalCell
  let n := ((Wiring.firstComputes Companion.shiftEncoding polynomialEncoding).andThen
    (Wiring.firstComputes coordinatesEncoding coordinatesEncoding)).andThen
      (WireLists.lengthComputes rationalEncoding)
  exact Executes.congr ((Executes.pair (Executes.ofComputes n) terms).comp Companion.sum)
    (fun p => Coordinates.evalAt_sum p.1.1 p.1.2 p.2)

end PolynomialEvaluation
end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
