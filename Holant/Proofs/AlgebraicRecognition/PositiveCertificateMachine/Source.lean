import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.Guard


namespace Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes coordinatesEncoding boxEncoding)
open Holant.LocalDrafts.Tractability.AffineMachine
open ComplexIsolation CertificateMachine

def relationPolynomial (c : List ℚ) : RationalPolynomialCode :=
  (c.length,1) :: CommonFieldMachine.Coordinates.tab c.length (fun i => (i,-c.getD i 0))
theorem relationPolynomial_ofFn {d : ℕ} (c : PowerArithmetic.Vector d) :
    relationPolynomial (List.ofFn c) = CommonPrimitive.relationCode c := by
  simp only [relationPolynomial,List.length_ofFn,CommonFieldMachine.Coordinates.tab_ofFn,
    getD_ofFn,CommonPrimitive.relationCode]

def certificateBox (t : Certificate) : RationalBox :=
  ⟨⟨t.center.1,t.radius⟩,⟨t.center.2,t.radius⟩⟩
theorem certificateBox_eq (t : Certificate) : certificateBox t = RationalBox.ofRectangle t.rectangle := by
  dsimp [certificateBox,RationalBox.ofRectangle,Certificate.rectangle,RationalBall.ofEndpoints]
  congr 2 <;> ring

noncomputable section
def familyComputes : Computes requestEncoding CommonFieldMachine.requestEncoding Request.family :=
  recode (Wiring.firstComputes CommonFieldMachine.requestEncoding
    (pairEncoding systemEncoding (pairEncoding vectorsEncoding CertificateMachine.certificateEncoding)))
    Request.wire (fun _ => rfl) (fun _ => rfl)
def remainderComputes : Computes requestEncoding
    (pairEncoding systemEncoding (pairEncoding vectorsEncoding CertificateMachine.certificateEncoding))
    (fun r => (r.equations,r.values,r.certificate)) :=
  recode (Wiring.secondComputes CommonFieldMachine.requestEncoding
    (pairEncoding systemEncoding (pairEncoding vectorsEncoding CertificateMachine.certificateEncoding)))
    Request.wire (fun _ => rfl) (fun _ => rfl)
def equationsComputes : Computes requestEncoding systemEncoding Request.equations :=
  remainderComputes.andThen (Wiring.firstComputes systemEncoding
    (pairEncoding vectorsEncoding CertificateMachine.certificateEncoding))
def valuesCertificateComputes : Computes requestEncoding
    (pairEncoding vectorsEncoding CertificateMachine.certificateEncoding) (fun r => (r.values,r.certificate)) :=
  remainderComputes.andThen (Wiring.secondComputes systemEncoding
    (pairEncoding vectorsEncoding CertificateMachine.certificateEncoding))
def valuesComputes : Computes requestEncoding vectorsEncoding Request.values :=
  valuesCertificateComputes.andThen (Wiring.firstComputes vectorsEncoding CertificateMachine.certificateEncoding)
def certificateComputes : Computes requestEncoding CertificateMachine.certificateEncoding Request.certificate :=
  valuesCertificateComputes.andThen (Wiring.secondComputes vectorsEncoding CertificateMachine.certificateEncoding)
def relationComputes := familyComputes.andThen CommonFieldMachine.FamilyMachine.relation
def sourceBoxComputes := familyComputes.andThen CommonFieldMachine.FamilyMachine.source
def expressionsComputes := familyComputes.andThen CommonFieldMachine.FamilyMachine.expressions
def targetsComputes := familyComputes.andThen CommonFieldMachine.FamilyMachine.targets
def dimensionComputes := familyComputes.andThen CommonFieldMachine.FamilyMachine.dimension

def relationPolynomialComputes : Computes coordinatesEncoding CertificateMachine.polynomialEncoding relationPolynomial := by
  let c := identityComputes coordinatesEncoding
  let n := c.andThen (WireLists.lengthComputes rationalEncoding)
  let cellInput := pairEncoding coordinatesEncoding UnaryBinary.unaryEncoding
  let xs := Wiring.firstComputes coordinatesEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes coordinatesEncoding UnaryBinary.unaryEncoding
  let q := Scalars.sub (constantComputes cellInput rationalEncoding 0)
    (AccessPrograms.get rationalEncoding 0 xs i)
  let cell := pairComputes (i.andThen UnaryBinary.computes) q
  let rest := WireLists.tabulate coordinatesEncoding CertificateMachine.termEncoding List.length n
    (fun c i => (i,-c.getD i 0)) (congrComputes cell (fun _ => by simp))
  let leading := pairComputes (n.andThen UnaryBinary.computes)
    (constantComputes coordinatesEncoding rationalEncoding 1)
  let singleton := fixedListComputes coordinatesEncoding CertificateMachine.termEncoding
    (fun c (_ : Unit) => (c.length,1)) (fun _ => leading) [()]
  exact congrComputes ((pairComputes singleton rest).andThen
    (WireLists.append CertificateMachine.termEncoding)) (fun _ => rfl)

def certificateBoxComputes : Computes CertificateMachine.certificateEncoding boxEncoding certificateBox := by
  let re := Scalars.real CertificateMachine.centerComputes
  let im := Scalars.imag CertificateMachine.centerComputes
  let r := CertificateMachine.radiusComputes
  exact recode (pairComputes (pairComputes re r) (pairComputes im r)) id (fun _ => rfl) (fun _ => rfl)

abbrev shapeContextEncoding := pairEncoding encodingNatBool encodingNatBool
def termShapeComputes : Computes (pairEncoding shapeContextEncoding termEncoding) encodingBoolBool
    (fun p => decide (p.2.1 < p.1.1 ∧ p.2.2.length = p.1.2)) := by
  let ctx := Wiring.firstComputes shapeContextEncoding termEncoding
  let t := Wiring.secondComputes shapeContextEncoding termEncoding
  let m := ctx.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let n := ctx.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  let i := t.andThen (Wiring.firstComputes encodingNatBool naturalsEncoding)
  let exps := t.andThen (Wiring.secondComputes encodingNatBool naturalsEncoding)
  let len := (exps.andThen (WireLists.lengthComputes encodingNatBool)).andThen UnaryBinary.computes
  exact congrComputes (AccessPrograms.bool Bool.and ((pairComputes i m).andThen Endpoints.lessComputes)
    (AccessPrograms.eqNat len n)) (fun _ => by simp)

def equationShapeComputes : Computes (pairEncoding shapeContextEncoding equationEncoding) encodingBoolBool
    (fun p => p.2.all (fun t => decide (t.1 < p.1.1 ∧ t.2.length = p.1.2))) :=
  congrComputes ((mapListComputes shapeContextEncoding termEncoding encodingBoolBool
    (fun c t => decide (t.1 < c.1 ∧ t.2.length = c.2)) termShapeComputes).andThen
      CommonFieldMachine.CoordinatePrimitives.allTrue) (fun _ => by simp [List.all_map])

def systemShapeComputes : Computes (pairEncoding shapeContextEncoding systemEncoding) encodingBoolBool
    (fun p => p.2.all (fun e => e.all (fun t => decide (t.1 < p.1.1 ∧ t.2.length = p.1.2)))) :=
  congrComputes ((mapListComputes shapeContextEncoding equationEncoding encodingBoolBool
    (fun c e => e.all (fun t => decide (t.1 < c.1 ∧ t.2.length = c.2))) equationShapeComputes).andThen
      CommonFieldMachine.CoordinatePrimitives.allTrue) (fun _ => by simp [List.all_map])

def shapeComputes : Computes requestEncoding encodingBoolBool Request.shape := by
  let n := (valuesComputes.andThen (WireLists.lengthComputes coordinatesEncoding)).andThen UnaryBinary.computes
  let m := (targetsComputes.andThen (WireLists.lengthComputes CertificateMachine.rootEncoding)).andThen UnaryBinary.computes
  let five := constantComputes requestEncoding encodingNatBool 5
  let enough := ((pairComputes n five).andThen Endpoints.lessComputes).andThen
    Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.negComputes
  let dim := Wiring.firstComputes encodingNatBool coordinatesEncoding
  let len := ((Wiring.secondComputes encodingNatBool coordinatesEncoding).andThen
    (WireLists.lengthComputes rationalEncoding)).andThen UnaryBinary.computes
  let lengths := (pairComputes dimensionComputes valuesComputes).andThen
    ((mapListComputes encodingNatBool coordinatesEncoding encodingBoolBool
      (fun d v => decide (v.length=d)) (AccessPrograms.eqNat len dim)).andThen
        CommonFieldMachine.CoordinatePrimitives.allTrue)
  let equations := (pairComputes (pairComputes m n) equationsComputes).andThen systemShapeComputes
  exact congrComputes (AccessPrograms.bool Bool.and
    (AccessPrograms.bool Bool.and
      (AccessPrograms.bool Bool.and (familyComputes.andThen CommonFieldMachine.FamilyMachine.shape) enough) lengths)
    equations) (fun r => by
      have enough_eq : (!decide (r.values.length < 5)) = decide (5 ≤ r.values.length) := by
        apply Bool.eq_iff_iff.mpr
        simp
      simpa [Request.shape,List.all_map] using congrArg
        (fun b => ((r.family.shape && b &&
          r.values.all (fun v => decide (v.length = r.family.dimension))) &&
          r.equations.all (fun e => e.all (fun t =>
            decide (t.1 < r.family.targets.length ∧ t.2.length = r.values.length))))) enough_eq)

end
end Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine
