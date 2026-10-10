import Holant.Proofs.Tractability.AffineMachine.FiniteFold
import Holant.Proofs.Tractability.ProductMachine.Bytecode
import Holant.Complexity.GraphPreprocessing.ListScan
import Holant.Complexity.GraphPreprocessing.ComponentSelection.UnaryRange


namespace Holant.LocalDrafts.Tractability.AffineMachine.WireLists

open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing StackProtocol
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding

variable {A B C : Type}

abbrev countMachine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Fin 3
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program i := if i = 0 then ListScan.markerStmt 0 1 0 1 2 2
    else if i = 1 then ListScan.skipStmt 0 1 0 2 else .halt

theorem count_run (e : Encoding A Bool) (xs : List A) :
    RunsExactly countMachine.computer.step
      (initList countMachine.computer ((framedListEncoding e).encode xs))
      (haltList countMachine.computer (List.replicate xs.length true)) (ListScan.ticks e xs + 1) := by
  have h := ListScan.count_exact (0 : Fin 2) 1 (by decide) countMachine.computer.step 0 1 2 2
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) e () (fun _ => []) xs [] []
  have last : countMachine.computer.step
      (cfg (2 : Fin 3) () (ListScan.tapes2 (fun _ => []) 0 1 [] (List.replicate xs.length true))) =
      some (haltList countMachine.computer (List.replicate xs.length true)) := by
    rw [Machine.halt_eq]
    simp [countMachine, TM2.step, TM2.stepAux, cfg, ListScan.tapes2, wordTape]
    rfl
  simp only [List.append_nil] at h
  have run := h.trans (runsExactly_one last)
  have ht : ListScan.tapes2 (fun _ : Fin 2 => []) 0 1 (framedListEncode e xs) [] =
      wordTape 0 (framedListEncode e xs) := by
    funext k
    fin_cases k <;> simp [ListScan.tapes2, wordTape]
  rw [Machine.init_eq]
  simpa only [ht, Nat.add_comm, framedListEncoding, cfg] using run

noncomputable def lengthComputes (e : Encoding A Bool) :
    Computes (framedListEncoding e) UnaryBinary.unaryEncoding List.length where
  machine := countMachine
  time := Polynomial.X + 1
  outputs xs := {
    steps := ListScan.ticks e xs + 1
    evals_in_steps := count_run e xs
    steps_le_m := by simpa [framedListEncoding] using Nat.add_le_add_right (ListScan.ticks_le_length e xs) 1 }

noncomputable def succComputes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding Nat.succ :=
  recode (joinComputes (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding [true])
    (encodeComputes UnaryBinary.unaryEncoding)) id (fun _ => rfl)
    (fun n => by simp [UnaryBinary.unaryEncoding, List.replicate_succ, Frame.wordEncoding])

noncomputable def mapComputes (ea : Encoding A Bool) (eb : Encoding B Bool)
    (f : A → B) (w : Computes ea eb f) :
    Computes (framedListEncoding ea) (framedListEncoding eb) (List.map f) := by
  let prepare := pairComputes (constantComputes (framedListEncoding ea) Frame.wordEncoding [])
    (identityComputes (framedListEncoding ea))
  exact congrComputes (prepare.andThen (mapListComputes Frame.wordEncoding ea eb
    (fun _ a => f a) ((Wiring.secondComputes Frame.wordEncoding ea).andThen w))) (fun _ => rfl)

noncomputable def append (e : Encoding A Bool) :
    Computes (pairEncoding (framedListEncoding e) (framedListEncoding e)) (framedListEncoding e)
      (fun x => x.1 ++ x.2) :=
  recode (joinComputes
    ((Wiring.firstComputes _ _).andThen (entriesComputes e))
    ((Wiring.secondComputes _ _).andThen (encodeComputes (framedListEncoding e)))) id (fun _ => rfl)
      (fun x => entries_append_encode e x.1 x.2)

noncomputable def replicate (e : Encoding A Bool) (a : A) :
    Computes UnaryBinary.unaryEncoding (framedListEncoding e) (fun n => List.replicate n a) :=
  congrComputes (ComponentSelection.UnaryRange.computes.andThen
    (mapComputes UnaryBinary.unaryEncoding e (fun _ => a)
      (constantComputes UnaryBinary.unaryEncoding e a))) (fun n => by simp)

def lookupEncoding (e : Encoding A Bool) := pairEncoding (framedListEncoding e) UnaryBinary.unaryEncoding

noncomputable def getD (e : Encoding A Bool) (default : A) :
    Computes (lookupEncoding e) e (fun x => x.1.getD x.2 default) := by
  let list := Wiring.firstComputes (framedListEncoding e) UnaryBinary.unaryEncoding
  let index := Wiring.secondComputes (framedListEncoding e) UnaryBinary.unaryEncoding
  let padding := (index.andThen succComputes).andThen (replicate e default)
  let padded := (pairComputes list padding).andThen (append e)
  let prepare : Computes (lookupEncoding e) (ParentRowSelect.inputEncoding e)
      (fun x => ⟨x.1 ++ List.replicate (x.2 + 1) default, paddedIndex x.1 x.2 default⟩) :=
    recode (pairComputes padded index) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen (ParentRowSelect.computes e))
    (fun x => padded_get x.1 x.2 default)

noncomputable def flatten (e : Encoding A Bool) :
    Computes (framedListEncoding (framedListEncoding e)) (framedListEncoding e) List.flatten := by
  let chunks := ProductMachine.Bytecode.flatMap (framedListEncoding e) _ (entriesComputes e)
  refine recode (joinComputes chunks
    (constantComputes (framedListEncoding (framedListEncoding e)) Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro xs
  change xs.flatMap (fun ys => ys.flatMap (entry e)) ++ [false] = framedListEncode e xs.flatten
  have hx : xs.flatMap (fun ys => ys.flatMap (entry e)) = entries e xs.flatten := by
    induction xs with
    | nil => rfl
    | cons ys xs ih =>
      simpa only [List.flatMap_cons, List.flatten_cons,
        FixedGadgetSubstitution.Compiler.entries, List.flatMap_append] using
          (congrArg (fun tail => ys.flatMap (entry e) ++ tail) ih)
  rw [hx]
  simpa only [List.append_nil, framedListEncode] using entries_append_encode e xs.flatten []

/-- General source-side tabulation over a computed PHYSICAL unary count. -/
noncomputable def tabulate (ea : Encoding A Bool) (eb : Encoding B Bool) (size : A → ℕ)
    (count : Computes ea UnaryBinary.unaryEncoding size) (f : A → ℕ → B)
    (cell : Computes (pairEncoding ea UnaryBinary.unaryEncoding) eb (fun x => f x.1 x.2)) :
    Computes ea (framedListEncoding eb) (fun a => (List.range (size a)).map (f a)) :=
  (pairComputes (identityComputes ea) (count.andThen ComponentSelection.UnaryRange.computes)).andThen
    (mapListComputes ea UnaryBinary.unaryEncoding eb f cell)

theorem lookup_primitive (e : Encoding A Bool) (default : A) (x : List A × ℕ) :
    let w := getD e default
    primitiveCost w.machine (w.outputs x).steps
      (some (initList w.machine.computer ((lookupEncoding e).encode x))) ≤
        (primitivePolynomial w).eval ((lookupEncoding e).encode x).length :=
  computes_primitive_cost (getD e default) x

end Holant.LocalDrafts.Tractability.AffineMachine.WireLists
