import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Companion


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Multiplication
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine

abbrev encoding := pairEncoding coordinatesEncoding Companion.shiftEncoding
abbrev outerEncoding := pairEncoding encoding UnaryBinary.unaryEncoding
abbrev innerEncoding := pairEncoding outerEncoding UnaryBinary.unaryEncoding

noncomputable def cell : Executes innerEncoding coordinatesEncoding
    (fun p => Coordinates.scale
      (Coordinates.at p.1.1.2.1 p.1.2 * Coordinates.at p.1.1.2.2 p.2)
      (Coordinates.power p.1.1.1 (p.1.2+p.2))) := by
  let outer := Wiring.firstComputes outerEncoding UnaryBinary.unaryEncoding
  let arg := outer.andThen (Wiring.firstComputes encoding UnaryBinary.unaryEncoding)
  let c := arg.andThen (Wiring.firstComputes coordinatesEncoding Companion.shiftEncoding)
  let uv := arg.andThen (Wiring.secondComputes coordinatesEncoding Companion.shiftEncoding)
  let u := uv.andThen (Wiring.firstComputes coordinatesEncoding coordinatesEncoding)
  let v := uv.andThen (Wiring.secondComputes coordinatesEncoding coordinatesEncoding)
  let i := outer.andThen (Wiring.secondComputes encoding UnaryBinary.unaryEncoding)
  let j := Wiring.secondComputes outerEncoding UnaryBinary.unaryEncoding
  let q := Scalars.mul (AccessPrograms.get rationalEncoding 0 u i)
    (AccessPrograms.get rationalEncoding 0 v j)
  let k := ((pairComputes i j).andThen AccessPrograms.unaryAdd).andThen UnaryBinary.computes
  let power := (Executes.ofComputes (pairComputes c k)).comp Companion.power
  exact (Executes.pair (Executes.ofComputes q) power).comp
    (Executes.ofComputes CoordinatePrimitives.scale)

noncomputable def row : Executes outerEncoding coordinatesEncoding
    (fun p => Coordinates.sum p.1.1.length (Coordinates.tab p.1.1.length
      (fun j => Coordinates.scale (Coordinates.at p.1.2.1 p.2 * Coordinates.at p.1.2.2 j)
        (Coordinates.power p.1.1 (p.2+j))))) := by
  let c := (Wiring.firstComputes encoding UnaryBinary.unaryEncoding).andThen
    (Wiring.firstComputes coordinatesEncoding Companion.shiftEncoding)
  let n := c.andThen (WireLists.lengthComputes rationalEncoding)
  let terms := Executes.tabulate outerEncoding coordinatesEncoding (fun p => p.1.1.length) n
    (fun p j => Coordinates.scale (Coordinates.at p.1.2.1 p.2 * Coordinates.at p.1.2.2 j)
      (Coordinates.power p.1.1 (p.2+j))) cell
  exact (Executes.pair (Executes.ofComputes n) terms).comp Companion.sum

noncomputable def mul : Executes encoding coordinatesEncoding
    (fun p => Coordinates.mul p.1 p.2.1 p.2.2) := by
  let n := (Wiring.firstComputes coordinatesEncoding Companion.shiftEncoding).andThen
    (WireLists.lengthComputes rationalEncoding)
  let rows := Executes.tabulate encoding coordinatesEncoding (fun p => p.1.length) n
    (fun p i => Coordinates.sum p.1.length (Coordinates.tab p.1.length
      (fun j => Coordinates.scale (Coordinates.at p.2.1 i * Coordinates.at p.2.2 j)
        (Coordinates.power p.1 (i+j))))) row
  exact (Executes.pair (Executes.ofComputes n) rows).comp Companion.sum

/-- State keeps relation, base and accumulator on three framed vector words. -/
def step (p : List ℚ × (List ℚ × List ℚ)) :=
  (p.1,p.2.1,Coordinates.mul p.1 p.2.2 p.2.1)
noncomputable def stepExecutes : Executes encoding encoding step := by
  let c := Wiring.firstComputes coordinatesEncoding Companion.shiftEncoding
  let va := Wiring.secondComputes coordinatesEncoding Companion.shiftEncoding
  let v := va.andThen (Wiring.firstComputes coordinatesEncoding coordinatesEncoding)
  let a := va.andThen (Wiring.secondComputes coordinatesEncoding coordinatesEncoding)
  let product := (Executes.ofComputes (pairComputes c (pairComputes a v))).comp mul
  exact Executes.pair (Executes.ofComputes c) (Executes.pair (Executes.ofComputes v) product)

theorem iterate_unit (c v : List ℚ) (k : ℕ) :
    (step^[k]) (c,v,Coordinates.unit c.length) = (c,v,Coordinates.powerAt c v k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

abbrev powerEncoding := pairEncoding Companion.shiftEncoding encodingNatBool
noncomputable def powerAt : Executes powerEncoding coordinatesEncoding
    (fun p => Coordinates.powerAt p.1.1 p.1.2 p.2) := by
  let cv := Wiring.firstComputes Companion.shiftEncoding encodingNatBool
  let n := Wiring.secondComputes Companion.shiftEncoding encodingNatBool
  let c := cv.andThen (Wiring.firstComputes coordinatesEncoding coordinatesEncoding)
  let v := cv.andThen (Wiring.secondComputes coordinatesEncoding coordinatesEncoding)
  let prepare := Executes.ofComputes (pairComputes n
    (pairComputes c (pairComputes v (c.andThen Companion.unit))))
  let loop := Iteration.executes encoding stepExecutes
  let extract := Executes.ofComputes
    ((Wiring.secondComputes coordinatesEncoding Companion.shiftEncoding).andThen
      (Wiring.secondComputes coordinatesEncoding coordinatesEncoding))
  exact Executes.congr ((prepare.comp loop).comp extract) (fun p => by
    change ((step^[p.2]) (p.1.1,p.1.2,Coordinates.unit p.1.1.length)).2.2 = _
    rw [iterate_unit])

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Multiplication
