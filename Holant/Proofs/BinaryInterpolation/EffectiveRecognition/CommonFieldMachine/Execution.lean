import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.BoxPower
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapRun


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient StackProtocol
open UniversalPairReduction.SmoothingCompiler
open FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding

structure Executes {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B) where
  machine : Machine
  cost : A → ℕ
  outputs : ∀ a, TM2OutputsInTime machine.computer (ea.encode a)
    (some (eb.encode (f a))) (cost a)

namespace Executes
variable {A B C D : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
  {ec : Encoding C Bool} {ed : Encoding D Bool}
noncomputable section

def ofComputes {f : A → B} (w : Computes ea eb f) : Executes ea eb f :=
  ⟨w.machine,fun a => w.time.eval (ea.encode a).length,w.outputs⟩

def comp {f : A → B} {g : B → C} (u : Executes ea eb f) (v : Executes eb ec g) :
    Executes ea ec (fun a => g (f a)) where
  machine := u.machine.compose v.machine
  cost a := u.cost a + 2*((eb.encode (f a)).length+1) + v.cost (f a)
  outputs a := Machine.compose_correct _ _ _ _ _ _ _ (u.outputs a) (v.outputs (f a))

def recode {f : A → B} {g : C → D} (w : Executes ea eb f) (input : C → A)
    (hi : ∀ c, ea.encode (input c) = ec.encode c)
    (ho : ∀ c, eb.encode (f (input c)) = ed.encode (g c)) : Executes ec ed g where
  machine := w.machine
  cost c := w.cost (input c)
  outputs c := by have h := w.outputs (input c); rw [hi,ho] at h; exact h

def congr {f g : A → B} (w : Executes ea eb f) (h : ∀ a,f a=g a) : Executes ea eb g :=
  recode w id (fun _ => rfl) (fun a => congrArg eb.encode (h a))

def leftMap {f : A → B} (ec : Encoding C Bool) (w : Executes ea eb f) :
    Executes (pairEncoding ea ec) (pairEncoding eb ec) (fun p => (f p.1,p.2)) where
  machine := LeftMap.machine w.machine
  cost p := 2*(ea.encode p.1).length+w.cost p.1+2*(eb.encode (f p.1)).length+6
  outputs p := {
    steps := 2*(ea.encode p.1).length+(w.outputs p.1).steps+2*(eb.encode (f p.1)).length+6
    evals_in_steps := LeftMap.exact_run w.machine _ _ _ _ (w.outputs p.1).evals_in_steps
    steps_le_m := by have h := (w.outputs p.1).steps_le_m; omega }

def rightMap {f : B → C} (ea : Encoding A Bool) (w : Executes eb ec f) :
    Executes (pairEncoding ea eb) (pairEncoding ea ec) (fun p => (p.1,f p.2)) :=
  ((ofComputes (Wiring.swapComputes ea eb)).comp (leftMap ea w)).comp
    (ofComputes (Wiring.swapComputes ec ea))

def pair {f : A → B} {g : A → C} (u : Executes ea eb f) (v : Executes ea ec g) :
    Executes ea (pairEncoding eb ec) (fun a => (f a,g a)) :=
  ((ofComputes (Wiring.diagonalComputes ea)).comp (leftMap ea u)).comp (rightMap eb v)

/-- The existing physical list controller is valid for arbitrary terminating
entry programs. Polynomial bounds in its old interface are not needed here. -/
def flatMap (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B → List Bool)
    (w : Executes (pairEncoding ea eb) Frame.wordEncoding (fun p => f p.1 p.2)) :
    Executes (pairEncoding ea (framedListEncoding eb)) Frame.wordEncoding
      (fun p => p.2.flatMap (f p.1)) where
  machine := ContextFlatMap.machine w.machine
  cost p := ContextFlatMap.ticks eb (ea.encode p.1) (f p.1) (fun b => w.cost (p.1,b)) p.2 +
    3*(ea.encode p.1).length+(p.2.flatMap (f p.1)).length+7
  outputs p := {
    steps := ContextFlatMap.ticks eb (ea.encode p.1) (f p.1)
      (fun b => (w.outputs (p.1,b)).steps) p.2 +
      3*(ea.encode p.1).length+(p.2.flatMap (f p.1)).length+7
    evals_in_steps := ContextFlatMap.whole w.machine eb (ea.encode p.1) (f p.1)
      (fun b => (w.outputs (p.1,b)).steps) p.2
      (fun b _ => (w.outputs (p.1,b)).evals_in_steps)
    steps_le_m := by
      have h : ContextFlatMap.ticks eb (ea.encode p.1) (f p.1)
          (fun b => (w.outputs (p.1,b)).steps) p.2 ≤
          ContextFlatMap.ticks eb (ea.encode p.1) (f p.1) (fun b => w.cost (p.1,b)) p.2 := by
        induction p.2 with
        | nil => rfl
        | cons b bs ih =>
          have hb := (w.outputs (p.1,b)).steps_le_m
          simp only [ContextFlatMap.ticks,List.map_cons,List.sum_cons] at *
          omega
      omega }

def mapList (ea : Encoding A Bool) (eb : Encoding B Bool) (ec : Encoding C Bool)
    (f : A → B → C) (w : Executes (pairEncoding ea eb) ec (fun p => f p.1 p.2)) :
    Executes (pairEncoding ea (framedListEncoding eb)) (framedListEncoding ec)
      (fun p => p.2.map (f p.1)) := by
  let entryProgram := w.comp (ofComputes (entryComputes ec))
  let raw := flatMap ea eb (fun a b => entry ec (f a b)) entryProgram
  let finish := ofComputes (joinComputes (identityComputes Frame.wordEncoding)
    (constantComputes Frame.wordEncoding Frame.wordEncoding [false]))
  refine recode (raw.comp finish) id (fun _ => rfl) ?_
  intro p
  have h : p.2.flatMap (fun b => entry ec (f p.1 b)) = entries ec (p.2.map (f p.1)) := by
    induction p.2 with
    | nil => rfl
    | cons b bs ih => simp [entries,ih]
  change p.2.flatMap (fun b => entry ec (f p.1 b)) ++ [false] =
    (framedListEncoding ec).encode (p.2.map (f p.1))
  rw [h]
  simpa only [List.append_nil,framedListEncoding,framedListEncode,Frame.wordEncoding] using
    entries_append_encode ec (p.2.map (f p.1)) []

def tabulate (ea : Encoding A Bool) (eb : Encoding B Bool) (n : A → ℕ)
    (count : Computes ea UnaryBinary.unaryEncoding n) (f : A → ℕ → B)
    (cell : Executes (pairEncoding ea UnaryBinary.unaryEncoding) eb (fun p => f p.1 p.2)) :
    Executes ea (framedListEncoding eb) (fun a => (List.range (n a)).map (f a)) :=
  (ofComputes (pairComputes (identityComputes ea)
    (count.andThen ComponentSelection.UnaryRange.computes))).comp
      (mapList ea UnaryBinary.unaryEncoding eb f cell)

theorem primitive_bound {f : A → B} (w : Executes ea eb f) (a : A) :
    primitiveCost w.machine (w.outputs a).steps
      (some (initList w.machine.computer (ea.encode a))) ≤ w.cost a*w.machine.primitiveBudget :=
  (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ (w.outputs a).steps_le_m)

theorem output_length {f : A → B} (w : Executes ea eb f) (a : A) :
    (eb.encode (f a)).length ≤ (ea.encode a).length+w.cost a*w.machine.primitiveBudget :=
  w.machine.output_length_le _ _ _ (w.outputs a)

end
end Executes
end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
