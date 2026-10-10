import Holant.Proofs.Recognition.PhysicalFolds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapRun

/-!
# Physical runtime list mapping on a proved source domain

The single cell machine is required to halt only on the actual members of each
runtime list, not on arbitrary malformed algebraic requests. The generic
controller calls every actual cell once in order, retains its bytes, and charges
all calls and list framing. No promise is tested by an oracle instruction: D and
membership proofs are erased correctness indices.

This is a controller combinator, not an algebraic evaluator producer. A final
recognizer must instantiate it with its constructed uniform cell programme and
prove the per-member source receipts without assuming the desired answer.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.PromisedListMap
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution.Compiler
open PhysicalFolds
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {D A X B : Type} {ea : Encoding A Bool} {ex : Encoding X Bool} {eb : Encoding B Bool}
variable (context : D → A) (items : D → List X)

abbrev Cell := Σ d : D, {x : X // x∈items d}
def cellInput (c : Cell items) : A × X := (context c.1,c.2.val)

variable {context items} {f : D → X → B}

def costAt (w : Runs (pairEncoding ea ex) eb (cellInput context items) (fun c => f c.1 c.2.val))
    (d : D) (x : X) : ℕ := by
  classical
  exact if h : x∈items d then w.cost ⟨d,⟨x,h⟩⟩ else 0

def stepsAt (w : Runs (pairEncoding ea ex) eb (cellInput context items) (fun c => f c.1 c.2.val))
    (d : D) (x : X) : ℕ := by
  classical
  exact if h : x∈items d then (w.outputs ⟨d,⟨x,h⟩⟩).steps else 0

theorem stepsAt_le (w : Runs (pairEncoding ea ex) eb (cellInput context items) (fun c => f c.1 c.2.val))
    (d : D) (x : X) (hx : x∈items d) : stepsAt w d x≤costAt w d x := by
  simp only [stepsAt,costAt,dif_pos hx]
  exact (w.outputs ⟨d,⟨x,hx⟩⟩).steps_le_m

private theorem ticks_mono (e : Encoding X Bool) (ctx : List Bool) (g : X → List Bool)
    (u v : X → ℕ) (xs : List X) (h : ∀x∈xs,u x≤v x) :
    ContextFlatMap.ticks e ctx g u xs≤ContextFlatMap.ticks e ctx g v xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have hs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [ContextFlatMap.ticks,List.map_cons,List.sum_cons] at *
    omega

/-- The list itself is runtime data; the cell programme has fixed control. -/
def flatMap {g : D → X → List Bool}
    (w : Runs (pairEncoding ea ex) Frame.wordEncoding (cellInput context items) (fun c => g c.1 c.2.val)) :
    Runs (pairEncoding ea (framedListEncoding ex)) Frame.wordEncoding
      (fun d => (context d,items d)) (fun d => (items d).flatMap (g d)) where
  machine := ContextFlatMap.machine w.machine
  cost d := ContextFlatMap.ticks ex (ea.encode (context d)) (g d) (costAt w d) (items d)+
    3*(ea.encode (context d)).length+((items d).flatMap (g d)).length+7
  outputs d := {
    steps := ContextFlatMap.ticks ex (ea.encode (context d)) (g d) (stepsAt w d) (items d)+
      3*(ea.encode (context d)).length+((items d).flatMap (g d)).length+7
    evals_in_steps := ContextFlatMap.whole w.machine ex (ea.encode (context d)) (g d)
      (stepsAt w d) (items d) (fun x hx => by
        have run := (w.outputs ⟨d,⟨x,hx⟩⟩).evals_in_steps
        change (fun c : Option w.machine.Config => c.bind w.machine.computer.step)^[
          (w.outputs ⟨d,⟨x,hx⟩⟩).steps]
          (some (initList w.machine.computer (frame (ea.encode (context d)) ++ ex.encode x)))=
          some (haltList w.machine.computer (g d x)) at run
        have hs : stepsAt w d x=(w.outputs ⟨d,⟨x,hx⟩⟩).steps := by
          simp only [stepsAt,dif_pos hx]
        rw [hs]
        exact run)
    steps_le_m := by
      have h := ticks_mono ex (ea.encode (context d)) (g d) (stepsAt w d) (costAt w d)
        (items d) (stepsAt_le w d)
      omega }

theorem flatMap_machine {g : D → X → List Bool}
    (w : Runs (pairEncoding ea ex) Frame.wordEncoding (cellInput context items) (fun c => g c.1 c.2.val)) :
    (flatMap w).machine=ContextFlatMap.machine w.machine := rfl

private def recodeOutput {C : Type} {ec : Encoding C Bool} {input : D → A}
    {output : D → B} {result : D → C} (w : Runs ea eb input output)
    (h : ∀d,eb.encode (output d)=ec.encode (result d)) : Runs ea ec input result where
  machine := w.machine
  cost := w.cost
  outputs d := by have out := w.outputs d; rw [h d] at out; exact out

/-- Emits a genuine framed list of the same physical returned cell values. -/
def mapList (w : Runs (pairEncoding ea ex) eb (cellInput context items) (fun c => f c.1 c.2.val)) :
    Runs (pairEncoding ea (framedListEncoding ex)) (framedListEncoding eb)
      (fun d => (context d,items d)) (fun d => (items d).map (f d)) := by
  let entryProgram := w.after (entryComputes eb)
  let raw := flatMap (context:=context) (items:=items) (g:=fun d x => entry eb (f d x)) entryProgram
  let finish := joinComputes (identityComputes Frame.wordEncoding)
    (constantComputes Frame.wordEncoding Frame.wordEncoding [false])
  apply recodeOutput (raw.after finish)
  intro d
  have h : (items d).flatMap (fun x => entry eb (f d x))=entries eb ((items d).map (f d)) := by
    induction items d with
    | nil => rfl
    | cons x xs ih => simp [entries,ih]
  change (items d).flatMap (fun x => entry eb (f d x)) ++ [false]=
    (framedListEncoding eb).encode ((items d).map (f d))
  rw [h]
  simpa only [List.append_nil,framedListEncoding,framedListEncode,Frame.wordEncoding] using
    entries_append_encode eb ((items d).map (f d)) []

theorem mapList_machine
    (w : Runs (pairEncoding ea ex) eb (cellInput context items) (fun c => f c.1 c.2.val)) :
    (mapList w).machine=(ContextFlatMap.machine (w.machine.compose (entryComputes eb).machine)).compose
      (joinComputes (identityComputes Frame.wordEncoding)
        (constantComputes Frame.wordEncoding Frame.wordEncoding [false])).machine := rfl

theorem output_length
    (w : Runs (pairEncoding ea ex) eb (cellInput context items) (fun c => f c.1 c.2.val)) (d : D) :
    ((framedListEncoding eb).encode ((items d).map (f d))).length≤
      ((pairEncoding ea (framedListEncoding ex)).encode (context d,items d)).length+
        (mapList w).cost d*(mapList w).machine.primitiveBudget :=
  (mapList w).machine.output_length_le _ _ _ ((mapList w).outputs d)

theorem resources (w : Runs (pairEncoding ea ex) eb (cellInput context items) (fun c => f c.1 c.2.val))
    (d : D) :
    let M := mapList w
    primitiveCost M.machine (M.outputs d).steps
      (some (initList M.machine.computer ((pairEncoding ea (framedListEncoding ex)).encode (context d,items d))))≤
      M.cost d*M.machine.primitiveBudget ∧
    ∀j, j≤(M.outputs d).steps → ∀cfg : M.machine.Config,
      (fun z => z.bind M.machine.computer.step)^[j]
        (some (initList M.machine.computer ((pairEncoding ea (framedListEncoding ex)).encode (context d,items d))))=some cfg →
      stackSize cfg.stk≤((pairEncoding ea (framedListEncoding ex)).encode (context d,items d)).length+
        M.cost d*M.machine.primitiveBudget := by
  let M := mapList w
  let out := M.outputs d
  refine ⟨(primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ out.steps_le_m),?_⟩
  intro j hj cfg hcfg
  have hs := M.machine.run_size_le _ cfg j hcfg
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hj.trans out.steps_le_m)) _)

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.PromisedListMap
