import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Coordinates
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.BoxPrimitives


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.CoordinatePrimitives
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine

noncomputable def scalarZero : Computes rationalEncoding encodingBoolBool (fun q => decide (q=0)) := by
  let z := constantComputes rationalEncoding rationalEncoding 0
  let q := identityComputes rationalEncoding
  let l := Scalars.less q z
  let r := Scalars.less z q
  exact congrComputes ((AccessPrograms.bool Bool.or l r).andThen
    Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.negComputes)
    (fun q => by
      by_cases h : q=0
      · subst q; simp
      · rcases lt_or_gt_of_ne h with h' | h' <;> simp [h,h'])

noncomputable def allTrue : Computes (framedListEncoding encodingBoolBool) encodingBoolBool
    (fun xs => xs.all id) :=
  congrComputes (FiniteFold.computes encodingBoolBool encodingBoolBool 1 Bool.and true
    (fun b => by cases b <;> rfl)) (fun xs => by
      have h : ∀ (bs : List Bool) (b : Bool), bs.foldl Bool.and b = (b && bs.all id) := by
        intro bs
        induction bs with
        | nil => intro b; simp
        | cons a bs ih => intro b; simp [ih, Bool.and_assoc]
      simpa using h xs true)

noncomputable def zero : Computes coordinatesEncoding encodingBoolBool Coordinates.isZero :=
  congrComputes ((WireLists.mapComputes rationalEncoding encodingBoolBool _ scalarZero).andThen allTrue)
    (fun xs => by simp [Coordinates.isZero, List.all_map])

noncomputable def scale : Computes (pairEncoding rationalEncoding coordinatesEncoding)
    coordinatesEncoding (fun p => Coordinates.scale p.1 p.2) :=
  mapListComputes rationalEncoding rationalEncoding rationalEncoding (fun q r => q*r)
    RationalArithmetic.multiplicationComputes

abbrev AddInput := ℕ × (List ℚ × List ℚ)
abbrev addEncoding := pairEncoding UnaryBinary.unaryEncoding
  (pairEncoding coordinatesEncoding coordinatesEncoding)

noncomputable def addCell : Computes (pairEncoding addEncoding UnaryBinary.unaryEncoding)
    rationalEncoding (fun p => Coordinates.at p.1.2.1 p.2 + Coordinates.at p.1.2.2 p.2) := by
  let arg := Wiring.firstComputes addEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes addEncoding UnaryBinary.unaryEncoding
  let lists := arg.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding
    (pairEncoding coordinatesEncoding coordinatesEncoding))
  let a := lists.andThen (Wiring.firstComputes coordinatesEncoding coordinatesEncoding)
  let b := lists.andThen (Wiring.secondComputes coordinatesEncoding coordinatesEncoding)
  exact Scalars.add (AccessPrograms.get rationalEncoding 0 a i)
    (AccessPrograms.get rationalEncoding 0 b i)

noncomputable def add : Computes addEncoding coordinatesEncoding
    (fun p => Coordinates.add p.1 p.2.1 p.2.2) :=
  WireLists.tabulate addEncoding rationalEncoding (fun p => p.1)
    (Wiring.firstComputes UnaryBinary.unaryEncoding (pairEncoding coordinatesEncoding coordinatesEncoding))
    (fun p i => Coordinates.at p.2.1 i + Coordinates.at p.2.2 i) addCell

/-- Relation length is measured from the supplied rational list. -/
noncomputable def addUsingRelation : Computes
    (pairEncoding coordinatesEncoding (pairEncoding coordinatesEncoding coordinatesEncoding))
    coordinatesEncoding (fun p => Coordinates.add p.1.length p.2.1 p.2.2) := by
  let n := (Wiring.firstComputes coordinatesEncoding
    (pairEncoding coordinatesEncoding coordinatesEncoding)).andThen
      (WireLists.lengthComputes rationalEncoding)
  let vs := Wiring.secondComputes coordinatesEncoding
    (pairEncoding coordinatesEncoding coordinatesEncoding)
  exact (pairComputes n vs).andThen add

theorem add_primitive (p : AddInput) :
    primitiveCost add.machine (add.outputs p).steps
      (some (Turing.initList add.machine.computer (addEncoding.encode p))) ≤
        (primitivePolynomial add).eval (addEncoding.encode p).length :=
  computes_primitive_cost add p

theorem zero_primitive (xs : List ℚ) :
    primitiveCost zero.machine (zero.outputs xs).steps
      (some (Turing.initList zero.machine.computer (coordinatesEncoding.encode xs))) ≤
        (primitivePolynomial zero).eval (coordinatesEncoding.encode xs).length :=
  computes_primitive_cost zero xs

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.CoordinatePrimitives
