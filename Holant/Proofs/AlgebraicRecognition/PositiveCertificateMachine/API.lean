import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.Source


namespace Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes coordinatesEncoding)
open Holant.LocalDrafts.MainChain.TransformRecognition
open ComplexIsolation

def coefficientValues (r : Request) : List (List ℚ) :=
  r.family.expressions.map (CommonFieldMachine.Coordinates.reduce r.family.relation)
def systemCheck (r : Request) : Bool :=
  SystemMachine.check (r.family.relation,coefficientValues r,r.values) r.equations
def check (r : Request) : Bool :=
  r.shape && (decide (r.family.box = certificateBox r.certificate) &&
    (r.certificate.check (relationPolynomial r.family.relation) &&
      ((CommonFieldMachine.check r.family && systemCheck r) && Guard.check r.family.relation r.values)))

theorem coefficientValues_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (s : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    coefficientValues (fromSource target s a) =
      List.ofFn (fun i => List.ofFn (CommonFieldCheck.familyCoordinates a.1.2.1 a.1.2.2.2.1 i)) := by
  simp only [coefficientValues,fromSource,CommonFieldMachine.fromFamily,List.map_ofFn,Function.comp_def,
    CommonFieldMachine.Coordinates.reduce_ofFn,CommonFieldCheck.familyCoordinates]

theorem systemCheck_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (s : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    systemCheck (fromSource target s a) =
      FixedSystem.checkSystem (PowerArithmetic.data a.1.2.1)
        (s.map (EncodedSystem.materialize (CommonFieldCheck.familyCoordinates a.1.2.1 a.1.2.2.2.1)))
        a.1.2.2.2.2 := by
  unfold systemCheck
  rw [coefficientValues_fromSource]
  exact SystemMachine.check_ofFn a.1.2.1
    (CommonFieldCheck.familyCoordinates a.1.2.1 a.1.2.2.2.1) a.1.2.2.2.2 s

/-- Exact Boolean equality, including source-box identity, root certification,
original conjugate identification, each original equation and the shared guard.
No relation irreducibility or satisfying assignment is assumed. -/
theorem check_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (s : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    check (fromSource target s a) = PositiveWitnessSearch.check target s a := by
  have hf : CommonFieldMachine.check (fromSource target s a).family =
      CommonFieldCheck.checkFamily a.1.2.1 a.1.2.2.1 a.1.2.2.2.1 target :=
    CommonFieldMachine.check_fromFamily _ _ _ _
  have hg : Guard.check (fromSource target s a).family.relation (fromSource target s a).values =
      MatrixWitness.checkGuard a.1.2.1 a.1.2.2.2.2 := Guard.check_ofFn _ _
  have hr : relationPolynomial (fromSource target s a).family.relation =
      CommonPrimitive.relationCode a.1.2.1 := relationPolynomial_ofFn _
  simp only [check,fromSource_shape,Bool.true_and,hf,hg,hr,systemCheck_fromSource,certificateBox_eq]
  rfl

theorem rejects_bad_shape {r : Request} (h : r.shape = false) : check r = false := by
  simp [check,h]

noncomputable section

def coefficientValuesExecutes : Executes requestEncoding vectorsEncoding coefficientValues :=
  (Executes.ofComputes (pairComputes relationComputes expressionsComputes)).comp
    (Executes.mapList coordinatesEncoding CertificateMachine.polynomialEncoding coordinatesEncoding
      CommonFieldMachine.Coordinates.reduce CommonFieldMachine.PolynomialEvaluation.reduce)

def systemExecutes : Executes requestEncoding encodingBoolBool systemCheck := by
  let context := (Executes.ofComputes relationComputes).pair
    (coefficientValuesExecutes.pair (Executes.ofComputes valuesComputes))
  exact (context.pair (Executes.ofComputes equationsComputes)).comp SystemMachine.systemExecutes

/-- Adapts the previously delivered length-cost root checker to the existing
input-cost composition interface; machine and outputs are unchanged. -/
def rootExecutes : Executes requestEncoding encodingBoolBool
    (fun r => r.certificate.check (relationPolynomial r.family.relation)) := by
  let prepare := Executes.ofComputes (pairComputes
    (relationComputes.andThen relationPolynomialComputes) certificateComputes)
  let w := CertificateMachine.computes
  let root : Executes CertificateMachine.inputEncoding encodingBoolBool
      (fun x : CertificateMachine.Input => x.2.check x.1) :=
    ⟨w.machine,fun x => w.time (CertificateMachine.inputEncoding.encode x).length,w.outputs⟩
  exact prepare.comp root

def sourceEqualityComputes : Computes requestEncoding encodingBoolBool
    (fun r => decide (r.family.box = certificateBox r.certificate)) :=
  (pairComputes sourceBoxComputes (certificateComputes.andThen certificateBoxComputes)).andThen
    (equalComputes CommonFieldMachine.boxEncoding)

/-- Every component is a concrete delivered program. There is no user-provided
checker/evaluator/cost witness and no free decode, field operation or halt. -/
def executes : Executes requestEncoding encodingBoolBool check := by
  let conjunction := Executes.ofComputes
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes
      (fun p : Bool × Bool => p.1 && p.2))
  let family := (Executes.ofComputes familyComputes).comp CommonFieldMachine.FamilyMachine.executes
  let system := (family.pair systemExecutes).comp conjunction
  let guard := (Executes.ofComputes (pairComputes relationComputes valuesComputes)).comp Guard.executes
  let precheck := (system.pair guard).comp conjunction
  let root := (rootExecutes.pair precheck).comp conjunction
  let boxed := ((Executes.ofComputes sourceEqualityComputes).pair root).comp conjunction
  exact ((Executes.ofComputes shapeComputes).pair boxed).comp conjunction

def outputs (r : Request) : TM2OutputsInTime executes.machine.computer
    (requestEncoding.encode r) (some (encodingBoolBool.encode (check r))) (executes.cost r) := executes.outputs r

def source_outputs {m k : ℕ} (target : Fin m → RootCode)
    (s : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    TM2OutputsInTime executes.machine.computer (requestEncoding.encode (fromSource target s a))
      (some (encodingBoolBool.encode (PositiveWitnessSearch.check target s a)))
      (executes.cost (fromSource target s a)) := by
  simpa only [check_fromSource] using executes.outputs (fromSource target s a)

def transitions (r : Request) : ℕ := executes.cost r
def primitives (r : Request) : ℕ := transitions r * executes.machine.primitiveBudget
def bits (r : Request) : ℕ := (requestEncoding.encode r).length + primitives r

theorem primitive_bound (r : Request) :
    primitiveCost executes.machine (executes.outputs r).steps
      (some (initList executes.machine.computer (requestEncoding.encode r))) ≤ primitives r :=
  executes.primitive_bound r

theorem prefix_bits (r : Request) {i : ℕ} (hi : i ≤ (executes.outputs r).steps)
    {c : executes.machine.Config}
    (hc : (fun s => s.bind executes.machine.computer.step)^[i]
      (some (initList executes.machine.computer (requestEncoding.encode r))) = some c) :
    stackSize c.stk ≤ bits r := by
  have h := executes.machine.run_size_le _ c i hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hi.trans (executes.outputs r).steps_le_m)) _)

/-- Root/solution existence follows only AFTER actual acceptance, by the
original source theorem. Original target representations identify the supplied
coefficients; they are not a proposed solution or a checker premise. -/
theorem accepted_sound {m k : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i, (target i).Represents (w i)) (s : EncodedSystem.System m (5+k))
    (a : PositiveWitnessSearch.Candidate m k) (ha : check (fromSource target s a) = true) :
    ∃ θ : ℂ, (a.2.rootCode (CommonPrimitive.relationCode a.1.2.1)).Represents θ ∧
      (∀ e ∈ s, MvPolynomial.aeval (fun j => PowerArithmetic.decode θ (a.1.2.2.2.2 j))
        (EncodedSystem.polynomial w e) = 0) ∧ MatrixWitness.checkGuard a.1.2.1 a.1.2.2.2.2 = true :=
  PositiveWitnessSearch.checked_sound target w ht s a ((check_fromSource target s a).symm.trans ha)

end
end Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine
