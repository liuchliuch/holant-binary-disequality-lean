import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.BoxEvaluation
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Checker


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.FamilyMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open ComplexIsolation.CertificateMachine (polynomialEncoding rootEncoding rectangleEncoding)
open Holant.LocalDrafts.Tractability.AffineMachine

noncomputable def rootPolynomial : Computes rootEncoding polynomialEncoding RootCode.coefficients :=
  recode (Wiring.firstComputes polynomialEncoding rectangleEncoding)
    (fun t : RootCode => (t.coefficients,t.rectangle)) (fun _ => rfl) (fun _ => rfl)
noncomputable def rootRectangle : Computes rootEncoding rectangleEncoding RootCode.rectangle :=
  recode (Wiring.secondComputes polynomialEncoding rectangleEncoding)
    (fun t : RootCode => (t.coefficients,t.rectangle)) (fun _ => rfl) (fun _ => rfl)

abbrev embeddingEncoding := pairEncoding coordinatesEncoding
  (pairEncoding boxEncoding (pairEncoding polynomialEncoding rootEncoding))

noncomputable def embeddingExecutes : Executes embeddingEncoding encodingBoolBool
    (fun p => embedding p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let c := Wiring.firstComputes coordinatesEncoding
    (pairEncoding boxEncoding (pairEncoding polynomialEncoding rootEncoding))
  let rest := Wiring.secondComputes coordinatesEncoding
    (pairEncoding boxEncoding (pairEncoding polynomialEncoding rootEncoding))
  let b := rest.andThen (Wiring.firstComputes boxEncoding (pairEncoding polynomialEncoding rootEncoding))
  let et := rest.andThen (Wiring.secondComputes boxEncoding (pairEncoding polynomialEncoding rootEncoding))
  let e := et.andThen (Wiring.firstComputes polynomialEncoding rootEncoding)
  let t := et.andThen (Wiring.secondComputes polynomialEncoding rootEncoding)
  let coord := (Executes.ofComputes (pairComputes c e)).comp PolynomialEvaluation.reduce
  let evalInput := Executes.pair (Executes.pair (Executes.ofComputes c) coord)
    (Executes.ofComputes (t.andThen rootPolynomial))
  let eq := (evalInput.comp PolynomialEvaluation.evalAt).comp (Executes.ofComputes CoordinatePrimitives.zero)
  let enclosure := (Executes.ofComputes (pairComputes b e)).comp BoxEvaluation.eval
  let rect := Executes.ofComputes (t.andThen rootRectangle)
  let inside := (Executes.pair enclosure rect).comp (Executes.ofComputes BoxPrimitives.inside)
  exact (Executes.pair eq inside).comp (Executes.ofComputes
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 && p.2)))

noncomputable def dimension : Computes requestEncoding encodingNatBool Request.dimension :=
  recode (Wiring.firstComputes encodingNatBool
    (pairEncoding coordinatesEncoding (pairEncoding boxEncoding (pairEncoding expressionsEncoding rootsEncoding))))
    Request.wire (fun _ => rfl) (fun _ => rfl)
noncomputable def relation : Computes requestEncoding coordinatesEncoding Request.relation :=
  recode ((Wiring.secondComputes encodingNatBool
    (pairEncoding coordinatesEncoding (pairEncoding boxEncoding (pairEncoding expressionsEncoding rootsEncoding)))).andThen
    (Wiring.firstComputes coordinatesEncoding (pairEncoding boxEncoding (pairEncoding expressionsEncoding rootsEncoding))))
    Request.wire (fun _ => rfl) (fun _ => rfl)
noncomputable def remainder : Computes requestEncoding
    (pairEncoding boxEncoding (pairEncoding expressionsEncoding rootsEncoding))
    (fun r => (r.box,r.expressions,r.targets)) :=
  recode ((Wiring.secondComputes encodingNatBool
    (pairEncoding coordinatesEncoding (pairEncoding boxEncoding (pairEncoding expressionsEncoding rootsEncoding)))).andThen
    (Wiring.secondComputes coordinatesEncoding (pairEncoding boxEncoding (pairEncoding expressionsEncoding rootsEncoding))))
    Request.wire (fun _ => rfl) (fun _ => rfl)
noncomputable def source : Computes requestEncoding boxEncoding Request.box :=
  remainder.andThen (Wiring.firstComputes boxEncoding (pairEncoding expressionsEncoding rootsEncoding))
noncomputable def expressions : Computes requestEncoding expressionsEncoding Request.expressions :=
  (remainder.andThen (Wiring.secondComputes boxEncoding (pairEncoding expressionsEncoding rootsEncoding))).andThen
    (Wiring.firstComputes expressionsEncoding rootsEncoding)
noncomputable def targets : Computes requestEncoding rootsEncoding Request.targets :=
  (remainder.andThen (Wiring.secondComputes boxEncoding (pairEncoding expressionsEncoding rootsEncoding))).andThen
    (Wiring.secondComputes expressionsEncoding rootsEncoding)

/-- Dimension and cardinality checks are finite tape programs too. -/
noncomputable def shape : Computes requestEncoding encodingBoolBool Request.shape := by
  let positive := (pairComputes (constantComputes requestEncoding encodingNatBool 0) dimension).andThen
    Endpoints.lessComputes
  let nc := (relation.andThen (WireLists.lengthComputes rationalEncoding)).andThen UnaryBinary.computes
  let ne := (expressions.andThen (WireLists.lengthComputes polynomialEncoding)).andThen UnaryBinary.computes
  let nt := (targets.andThen (WireLists.lengthComputes rootEncoding)).andThen UnaryBinary.computes
  exact congrComputes (AccessPrograms.bool Bool.and positive
    (AccessPrograms.bool Bool.and (AccessPrograms.eqNat nc dimension) (AccessPrograms.eqNat ne nt)))
    (fun r => by simp [Request.shape])

/-- Only used beyond a malformed list's end; shape then rejects the request. -/
def defaultRoot : RootCode := ⟨[],⟨0,0,0,0⟩⟩
def entry (r : Request) (i : ℕ) : Bool := embedding r.relation r.box
  (r.expressions.getD i []) (r.targets.getD i defaultRoot)

noncomputable def entryExecutes : Executes (pairEncoding requestEncoding UnaryBinary.unaryEncoding)
    encodingBoolBool (fun p => entry p.1 p.2) := by
  let r := Wiring.firstComputes requestEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes requestEncoding UnaryBinary.unaryEncoding
  let e := AccessPrograms.get polynomialEncoding [] (r.andThen expressions) i
  let t := AccessPrograms.get rootEncoding defaultRoot (r.andThen targets) i
  let prepare := pairComputes (r.andThen relation)
    (pairComputes (r.andThen source) (pairComputes e t))
  exact (Executes.ofComputes prepare).comp embeddingExecutes

def scan (r : Request) : Bool :=
  r.shape && ((List.range r.expressions.length).map (entry r)).all id

noncomputable def scanExecutes : Executes requestEncoding encodingBoolBool scan := by
  let count := expressions.andThen (WireLists.lengthComputes polynomialEncoding)
  let values := Executes.tabulate requestEncoding encodingBoolBool
    (fun r => r.expressions.length) count entry entryExecutes
  let accepted := values.comp (Executes.ofComputes CoordinatePrimitives.allTrue)
  exact (Executes.pair (Executes.ofComputes shape) accepted).comp (Executes.ofComputes
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 && p.2)))

theorem range_family (c : List ℚ) (b : RationalBox) (es : List RationalPolynomialCode)
    (ts : List RootCode) (h : es.length=ts.length) :
    ((List.range es.length).map (fun i => embedding c b (es.getD i [])
      (ts.getD i defaultRoot))).all id = family c b es ts := by
  induction es generalizing ts with
  | nil => cases ts <;> simp_all [family]
  | cons e es ih =>
    cases ts with
    | nil => simp at h
    | cons t ts =>
      have ht : es.length=ts.length := by simpa using h
      simpa [List.range_succ_eq_map,List.map_map,Function.comp_def,family] using
        congrArg (fun v => embedding c b e t && v) (ih ts ht)

theorem scan_eq_check (r : Request) : scan r = check r := by
  by_cases h : r.shape=true
  · have hn := (shape_iff r).mp h
    simp only [scan,check,h,Bool.true_and]
    exact range_family r.relation r.box r.expressions r.targets hn.2.2
  · have hf : r.shape=false := Bool.eq_false_iff.mpr h
    simp [scan,check,hf]

/-- Full finite Boolean-stack checker, with all providers instantiated. -/
noncomputable def executes : Executes requestEncoding encodingBoolBool check :=
  Executes.congr scanExecutes scan_eq_check

noncomputable def source_outputs {d m : ℕ} (c : PowerArithmetic.Vector d) (b : RationalBox)
    (e : Fin m → RationalPolynomialCode) (t : Fin m → RootCode) :
    TM2OutputsInTime executes.machine.computer
      (requestEncoding.encode (fromFamily c b e t))
      (some (encodingBoolBool.encode (CommonFieldCheck.checkFamily c b e t)))
      (executes.cost (fromFamily c b e t)) := by
  simpa only [check_fromFamily] using executes.outputs (fromFamily c b e t)

theorem primitive_bound (r : Request) :
    primitiveCost executes.machine (executes.outputs r).steps
      (some (initList executes.machine.computer (requestEncoding.encode r))) ≤
        executes.cost r*executes.machine.primitiveBudget := executes.primitive_bound r

theorem output_bound (r : Request) :
    (encodingBoolBool.encode (check r)).length ≤ (requestEncoding.encode r).length+
      executes.cost r*executes.machine.primitiveBudget := executes.output_length r

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.FamilyMachine
