import Holant.Proofs.Tractability.AffineMachine.AccessPrograms
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Execution

/-!
# Generic physical composition and finite folds

These additive wrappers reuse the established physical composition, fanout,
encoding and Boolean programmes. They deliberately do not import EO semantics.
The source datum indexes the correctness proof, not the machine input; no
semantic evaluator or termination oracle is a runtime argument.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.PhysicalFolds
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler

structure Runs {D A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
    (input : D → A) (output : D → B) where
  machine : BinaryCompose.Machine
  cost : D → ℕ
  outputs : ∀ d, TM2OutputsInTime machine.computer (ea.encode (input d))
    (some (eb.encode (output d))) (cost d)

namespace Runs
variable {D A B C : Type} {ea : Encoding A Bool} {eb : Encoding B Bool} {ec : Encoding C Bool}
variable {input : D → A} {middle : D → B} {output : D → C}
noncomputable section

def ofComputes {f : A → B} (w : Computes ea eb f) (input : D → A) :
    Runs ea eb input (fun d => f (input d)) :=
  ⟨w.machine,fun d => w.time.eval (ea.encode (input d)).length,fun d => w.outputs (input d)⟩

def comp (u : Runs ea eb input middle) (v : Runs eb ec middle output) :
    Runs ea ec input output where
  machine := u.machine.compose v.machine
  cost d := u.cost d+2*((eb.encode (middle d)).length+1)+v.cost d
  outputs d := BinaryCompose.Machine.compose_correct _ _ _ _ _ _ _ (u.outputs d) (v.outputs d)

def after {f : B → C} (u : Runs ea eb input middle) (v : Computes eb ec f) :
    Runs ea ec input (fun d => f (middle d)) := u.comp (ofComputes v middle)

def congr (u : Runs ea eb input middle) {g : D → B} (h : ∀ d, middle d=g d) :
    Runs ea eb input g where
  machine := u.machine
  cost := u.cost
  outputs d := by simpa only [h d] using u.outputs d

def constant (ea : Encoding A Bool) (eb : Encoding B Bool) (input : D → A) (b : B) :
    Runs ea eb input (fun _ => b) := ofComputes (constantComputes ea eb b) input

def leftMap (ec : Encoding C Bool) (suffix : D → C) (w : Runs ea eb input middle) :
    Runs (pairEncoding ea ec) (pairEncoding eb ec)
      (fun d => (input d,suffix d)) (fun d => (middle d,suffix d)) where
  machine := LeftMap.machine w.machine
  cost d := 2*(ea.encode (input d)).length+w.cost d+2*(eb.encode (middle d)).length+6
  outputs d := {
    steps := 2*(ea.encode (input d)).length+(w.outputs d).steps+2*(eb.encode (middle d)).length+6
    evals_in_steps := LeftMap.exact_run w.machine _ _ _ _ (w.outputs d).evals_in_steps
    steps_le_m := by have h := (w.outputs d).steps_le_m; omega }

def rightMap (ea : Encoding A Bool) (saved : D → A) (w : Runs eb ec middle output) :
    Runs (pairEncoding ea eb) (pairEncoding ea ec)
      (fun d => (saved d,middle d)) (fun d => (saved d,output d)) :=
  ((ofComputes (Wiring.swapComputes ea eb) (fun d => (saved d,middle d))).comp
    (leftMap ea saved w)).after (Wiring.swapComputes ec ea)

def pair (u : Runs ea eb input middle) (v : Runs ea ec input output) :
    Runs ea (pairEncoding eb ec) input (fun d => (middle d,output d)) :=
  ((ofComputes (Wiring.diagonalComputes ea) input).comp (leftMap ea input u)).comp
    (rightMap eb middle v)

def bool {f g : D → Bool} (op : Bool → Bool → Bool)
    (u : Runs ea encodingBoolBool input f) (v : Runs ea encodingBoolBool input g) :
    Runs ea encodingBoolBool input (fun d => op (f d) (g d)) :=
  (u.pair v).after (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes
    (fun p => op p.1 p.2))

private def selectComputes (eb : Encoding B Bool) :
    Computes (pairEncoding encodingBoolBool (pairEncoding eb eb)) eb
      (fun x => if x.1 then x.2.1 else x.2.2) :=
  ifComputes (Wiring.firstComputes encodingBoolBool (pairEncoding eb eb))
    ((Wiring.secondComputes encodingBoolBool (pairEncoding eb eb)).andThen (Wiring.firstComputes eb eb))
    ((Wiring.secondComputes encodingBoolBool (pairEncoding eb eb)).andThen (Wiring.secondComputes eb eb))

/-- The physical selector computes all three supplied runs, then reads its
actual Bool and selects a framed candidate. The cost charges all three runs. -/
def choose {p : D → Bool} {f g : D → B}
    (test : Runs ea encodingBoolBool input p) (yes : Runs ea eb input f) (no : Runs ea eb input g) :
    Runs ea eb input (fun d => if p d then f d else g d) :=
  (test.pair (yes.pair no)).after (selectComputes eb)

def all {X : Type} (test : D → X → Bool)
    (w : ∀ x, Runs ea encodingBoolBool input (fun d => test d x)) :
    (xs : List X) → Runs ea encodingBoolBool input (fun d => xs.all (test d))
  | [] => constant ea encodingBoolBool input true
  | x::xs => (bool Bool.and (w x) (all test w xs)).congr (fun d => by simp)

def any {X : Type} (test : D → X → Bool)
    (w : ∀ x, Runs ea encodingBoolBool input (fun d => test d x)) :
    (xs : List X) → Runs ea encodingBoolBool input (fun d => xs.any (test d))
  | [] => constant ea encodingBoolBool input false
  | x::xs => (bool Bool.or (w x) (any test w xs)).congr (fun d => by simp)

def first {X : Type} (ex : Encoding X Bool) (test : D → X → Bool)
    (w : ∀ x, Runs ea encodingBoolBool input (fun d => test d x)) :
    (xs : List X) → Runs ea (Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding ex) input
      (fun d => (xs.filter (test d)).head?)
  | [] => constant ea _ input none
  | x::xs => (choose (w x) (constant ea _ input (some x)) (first ex test w xs)).congr
      (fun d => by cases h : test d x <;> simp [h])

end
end Runs
end Holant.LocalDrafts.RemoteWork.TractChainV1.PhysicalFolds
