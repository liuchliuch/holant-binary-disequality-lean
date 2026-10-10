import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Iteration
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.CoordinatePrimitives
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.RationalFold


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Companion
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine

abbrev sumEncoding := pairEncoding UnaryBinary.unaryEncoding (framedListEncoding coordinatesEncoding)
abbrev sumCellEncoding := pairEncoding sumEncoding UnaryBinary.unaryEncoding

noncomputable def column : Computes sumCellEncoding coordinatesEncoding
    (fun p => p.1.2.map (fun v => Coordinates.at v p.2)) := by
  let p := Wiring.firstComputes sumEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes sumEncoding UnaryBinary.unaryEncoding
  let vs := p.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding
    (framedListEncoding coordinatesEncoding))
  let cell := (pairComputes (Wiring.secondComputes UnaryBinary.unaryEncoding coordinatesEncoding)
    (Wiring.firstComputes UnaryBinary.unaryEncoding coordinatesEncoding)).andThen
      (WireLists.getD rationalEncoding 0)
  exact (pairComputes i vs).andThen (mapListComputes UnaryBinary.unaryEncoding coordinatesEncoding
    rationalEncoding (fun i v => Coordinates.at v i) cell)

noncomputable def rationalSum : Executes coordinatesEncoding rationalEncoding List.sum :=
  ⟨RationalFold.machine,RationalFold.bound,RationalFold.outputs⟩

noncomputable def sum : Executes sumEncoding coordinatesEncoding
    (fun p => Coordinates.sum p.1 p.2) :=
  Executes.tabulate sumEncoding rationalEncoding (fun p => p.1)
    (Wiring.firstComputes UnaryBinary.unaryEncoding (framedListEncoding coordinatesEncoding))
    (fun p i => (p.2.map (fun v => Coordinates.at v i)).sum)
    ((Executes.ofComputes column).comp rationalSum)

abbrev basisEncoding := pairEncoding coordinatesEncoding UnaryBinary.unaryEncoding

noncomputable def basisCell : Computes (pairEncoding basisEncoding UnaryBinary.unaryEncoding)
    rationalEncoding (fun p => if p.2 = p.1.2+1 then 1 else 0) := by
  let p := Wiring.firstComputes basisEncoding UnaryBinary.unaryEncoding
  let i := (p.andThen (Wiring.secondComputes coordinatesEncoding UnaryBinary.unaryEncoding)).andThen
    WireLists.succComputes
  let j := Wiring.secondComputes basisEncoding UnaryBinary.unaryEncoding
  let eq := AccessPrograms.eqNat (j.andThen UnaryBinary.computes) (i.andThen UnaryBinary.computes)
  exact congrComputes (ifComputes eq (constantComputes _ rationalEncoding 1)
    (constantComputes _ rationalEncoding 0)) (fun p => by simp)

noncomputable def basisStep : Computes basisEncoding coordinatesEncoding
    (fun p => Coordinates.basisStep p.1 p.2) := by
  let c := Wiring.firstComputes coordinatesEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes coordinatesEncoding UnaryBinary.unaryEncoding
  let n := c.andThen (WireLists.lengthComputes rationalEncoding)
  let test := (pairComputes ((i.andThen WireLists.succComputes).andThen UnaryBinary.computes)
    (n.andThen UnaryBinary.computes)).andThen Endpoints.lessComputes
  let basis := WireLists.tabulate basisEncoding rationalEncoding (fun p => p.1.length) n
    (fun p j => if j=p.2+1 then 1 else 0) basisCell
  exact congrComputes (ifComputes test basis c) (fun p => by simp [Coordinates.basisStep,Coordinates.tab])

abbrev shiftEncoding := pairEncoding coordinatesEncoding coordinatesEncoding

noncomputable def shiftCell : Computes (pairEncoding shiftEncoding UnaryBinary.unaryEncoding)
    coordinatesEncoding (fun p => Coordinates.scale (Coordinates.at p.1.2 p.2)
      (Coordinates.basisStep p.1.1 p.2)) := by
  let p := Wiring.firstComputes shiftEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes shiftEncoding UnaryBinary.unaryEncoding
  let c := p.andThen (Wiring.firstComputes coordinatesEncoding coordinatesEncoding)
  let v := p.andThen (Wiring.secondComputes coordinatesEncoding coordinatesEncoding)
  let coefficient := AccessPrograms.get rationalEncoding 0 v i
  let basis := (pairComputes c i).andThen basisStep
  exact (pairComputes coefficient basis).andThen CoordinatePrimitives.scale

noncomputable def shift : Executes shiftEncoding coordinatesEncoding
    (fun p => Coordinates.shift p.1 p.2) := by
  let n := (Wiring.firstComputes coordinatesEncoding coordinatesEncoding).andThen
    (WireLists.lengthComputes rationalEncoding)
  let terms := WireLists.tabulate shiftEncoding coordinatesEncoding (fun p => p.1.length) n
    (fun p i => Coordinates.scale (Coordinates.at p.2 i) (Coordinates.basisStep p.1 i)) shiftCell
  exact (Executes.ofComputes (pairComputes n terms)).comp sum

noncomputable def unit : Computes coordinatesEncoding coordinatesEncoding
    (fun c => Coordinates.unit c.length) := by
  let cell := ifComputes
    (AccessPrograms.eqNat
      ((Wiring.secondComputes coordinatesEncoding UnaryBinary.unaryEncoding).andThen UnaryBinary.computes)
      (constantComputes _ encodingNatBool 0))
    (constantComputes _ rationalEncoding 1) (constantComputes _ rationalEncoding 0)
  exact WireLists.tabulate coordinatesEncoding rationalEncoding List.length
    (WireLists.lengthComputes rationalEncoding) (fun _ i => if i=0 then 1 else 0)
    (congrComputes cell (fun p => by simp))

def step (p : List ℚ × List ℚ) := (p.1,Coordinates.shift p.1 p.2)
noncomputable def stepExecutes : Executes shiftEncoding shiftEncoding step :=
  Executes.pair (Executes.ofComputes (Wiring.firstComputes coordinatesEncoding coordinatesEncoding)) shift

theorem iterate_unit (c : List ℚ) (k : ℕ) :
    (step^[k]) (c,Coordinates.unit c.length) = (c,Coordinates.power c k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

abbrev powerEncoding := pairEncoding coordinatesEncoding encodingNatBool
noncomputable def power : Executes powerEncoding coordinatesEncoding (fun p => Coordinates.power p.1 p.2) := by
  let c := Wiring.firstComputes coordinatesEncoding encodingNatBool
  let n := Wiring.secondComputes coordinatesEncoding encodingNatBool
  let prepare := Executes.ofComputes (pairComputes n (pairComputes c (c.andThen unit)))
  let loop := Iteration.executes shiftEncoding stepExecutes
  let out := Executes.ofComputes (Wiring.secondComputes coordinatesEncoding coordinatesEncoding)
  exact Executes.congr ((prepare.comp loop).comp out) (fun p => by
    change ((step^[p.2]) (p.1,Coordinates.unit p.1.length)).2 = _
    rw [iterate_unit])

theorem power_primitive (p : List ℚ × ℕ) :
    primitiveCost power.machine (power.outputs p).steps
      (some (Turing.initList power.machine.computer (powerEncoding.encode p))) ≤
        power.cost p*power.machine.primitiveBudget := power.primitive_bound p

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Companion
