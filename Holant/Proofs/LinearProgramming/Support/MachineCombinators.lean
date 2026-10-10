import Holant.Proofs.LinearProgramming.Support.MachineCombinators.FiniteFold
import Holant.Proofs.LinearProgramming.Support.MachineCombinators.WordCompare
import Holant.Proofs.LinearProgramming.Support.MachineCombinators.UnaryRange
import Holant.Proofs.LinearProgramming.Support.MachineCombinators.EncodedComparison
import Holant.Proofs.LinearProgramming.Support.MachineCombinators.EncodedSubtraction
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists
import Holant.Complexity.GraphPreprocessing.FiniteRecode
import Holant.Complexity.FixedFieldMachines.PrimitiveCost
open Holant.Complexity
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable {A B C : Type}
noncomputable def chooseComputes (ea : Encoding A Bool) (eb : Encoding B Bool) (n : ℕ)
    (label : A → Fin n) (f : A → Fin n → B)
    (index : Computes ea UnaryBinary.unaryEncoding (fun a => (label a).val))
    (w : ∀ i, Computes ea eb (fun a => f a i)) :
    Computes ea eb (fun a => f a (label a)) := by
  let output (a : A) := (List.finRange n).map (f a)
  let selectedIndex (a : A) : Fin (output a).length := ⟨(label a).val,by simpa [output] using (label a).isLt⟩
  let prepare : Computes ea (ParentRowSelect.inputEncoding eb)
      (fun a => ⟨output a,selectedIndex a⟩) :=
    recode (pairComputes (fixedListComputes ea eb f w (List.finRange n)) index)
      id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen (ParentRowSelect.computes eb))
    (fun a => by simp [ParentRowSelect.selected,output,selectedIndex,List.get_eq_getElem])

def boolIndex (b : Bool) : Fin 2 := if b then 1 else 0
noncomputable def boolIndexComputes : Computes encodingBoolBool UnaryBinary.unaryEncoding
    (fun b => (boolIndex b).val) :=
  FiniteRecode.computes encodingBoolBool UnaryBinary.unaryEncoding
    (fun b => (boolIndex b).val) 1 (fun b => by cases b <;> decide)

/-- Both candidates are computed by fixed finite programs; a literal list-index
program chooses one using the computed Boolean. -/
noncomputable def ifComputes {ea : Encoding A Bool} {eb : Encoding B Bool}
    {p : A → Bool} {f g : A → B} (test : Computes ea encodingBoolBool p)
    (yes : Computes ea eb f) (no : Computes ea eb g) :
    Computes ea eb (fun a => if p a then f a else g a) := by
  let candidates (a : A) (i : Fin 2) := if i.val=1 then f a else g a
  let w (i : Fin 2) : Computes ea eb (fun a => candidates a i) := by
    by_cases h : i.val=1
    · exact congrComputes yes (fun _ => by simp [candidates,h])
    · exact congrComputes no (fun _ => by simp [candidates,h])
  refine congrComputes (chooseComputes ea eb 2 (fun a => boolIndex (p a)) candidates
    (test.andThen boolIndexComputes) w) ?_
  intro a
  cases h : p a <;> simp [candidates,boolIndex,h]

noncomputable def equalComputes [DecidableEq A] (e : Encoding A Bool) :
    Computes (pairEncoding e e) encodingBoolBool (fun x => decide (x.1=x.2)) := by
  classical
  refine recode WordCompare.computes (fun x => (e.encode x.1,e.encode x.2))
    (fun _ => rfl) ?_
  intro x
  have he : e.encode x.1=e.encode x.2 ↔ x.1=x.2 :=
    ⟨fun h => Option.some.inj ((e.decode_encode x.1).symm.trans
      ((congrArg e.decode h).trans (e.decode_encode x.2))),congrArg e.encode⟩
  simp only [WordCompare.value,he]

/-- Traverse every physical input element, preserving order and all frames. -/
noncomputable def mapListComputes (ea : Encoding A Bool) (eb : Encoding B Bool)
    (ec : Encoding C Bool) (f : A → B → C)
    (w : Computes (pairEncoding ea eb) ec (fun x => f x.1 x.2)) :
    Computes (pairEncoding ea (framedListEncoding eb)) (framedListEncoding ec)
      (fun x => x.2.map (f x.1)) := by
  let provider : Computes (sigmaEncoding ea (fun _ => eb)) Frame.wordEncoding
      (fun x => entry ec (f x.1 x.2)) :=
    recode (w.andThen (entryComputes ec)) (fun x => (x.1,x.2))
      (fun _ => rfl) (fun _ => rfl)
  let run : Computes (pairEncoding ea (framedListEncoding eb)) Frame.wordEncoding
      (fun x => x.2.flatMap (fun b => entry ec (f x.1 b))) :=
    recode (ContextFlatMap.computes ea (fun _ => eb) _ provider)
      (fun x => ⟨x.1,x.2⟩) (fun _ => rfl) (fun _ => rfl)
  refine recode (joinComputes run
    (constantComputes (pairEncoding ea (framedListEncoding eb)) Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro x
  have h := entries_append_encode ec (x.2.map (f x.1)) []
  simpa only [entries,List.flatMap_map,Function.comp_def,List.append_nil,framedListEncode,
    Frame.wordEncoding,framedListEncoding,id_eq] using h

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Bytecode
open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {A : Type}
noncomputable def flatMap (ea : Encoding A Bool) (f : A → List Bool)
    (w : Computes ea Frame.wordEncoding f) :
    Computes (framedListEncoding ea) Frame.wordEncoding (fun xs => xs.flatMap f) := by
  let prepare : Computes (framedListEncoding ea)
      (ContextFlatMap.inputEncoding Frame.wordEncoding (fun _ => ea))
      (fun xs => (⟨[], xs⟩ : Σ _ : List Bool, List A)) :=
    recode (pairComputes (constantComputes (framedListEncoding ea) Frame.wordEncoding [])
      (identityComputes (framedListEncoding ea))) id (fun _ => rfl) (fun _ => rfl)
  let worker : Computes (sigmaEncoding Frame.wordEncoding (fun _ => ea)) Frame.wordEncoding
      (fun x => f x.2) :=
    recode ((Wiring.secondComputes Frame.wordEncoding ea).andThen w)
      (fun x => (x.1, x.2)) (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ContextFlatMap.computes Frame.wordEncoding (fun _ => ea) _ worker)


end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Bytecode

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Endpoints
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open GraphPreprocessing.OriginalCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev natPairEncoding := pairEncoding encodingNatBool encodingNatBool

abbrev comparisonMachine : Machine where
  K := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.computer.K
  input := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.computer.k₀
  output := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.computer.k₁
  Label := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.computer.Λ
  main := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.computer.main
  State := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.computer.σ
  initial := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.computer.initialState
  program := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.computer.m

abbrev subtractionMachine : Machine where
  K := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.computer.K
  input := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.computer.k₀
  output := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.computer.k₁
  Label := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.computer.Λ
  main := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.computer.main
  State := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.computer.σ
  initial := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.computer.initialState
  program := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.computer.m

noncomputable def prepareArithmeticComputes :
    Computes natPairEncoding BinaryArithmetic.EncodedAddition.inputEncoding id :=
  recode (pairComputes
    ((Wiring.firstComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
    ((Wiring.secondComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool)))
    id (fun _ => rfl) (fun _ => rfl)

noncomputable def encodedComparisonComputes :
    Computes Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.inputEncoding encodingBoolBool
      (fun p => decide (p.1 < p.2)) where
  machine := comparisonMachine
  time := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.comparisonPolyTime.time
  outputs p := by
    have h := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.comparisonPolyTime.outputsFun p
    change TM2OutputsInTime comparisonMachine.computer
      (List.map id (Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedComparison.inputEncoding.encode p))
      (some (List.map id (encodingBoolBool.encode (decide (p.1 < p.2))))) _ at h
    simpa only [List.map_id] using h

noncomputable def encodedSubtractionComputes :
    Computes Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.inputEncoding encodingNatBool
      (fun p => p.1 - p.2) where
  machine := subtractionMachine
  time := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.subtractionPolyTime.time
  outputs p := by
    have h := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.subtractionPolyTime.outputsFun p
    change TM2OutputsInTime subtractionMachine.computer
      (List.map id (Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.EncodedSubtraction.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1 - p.2)))) _ at h
    simpa only [List.map_id] using h

noncomputable def lessComputes : Computes natPairEncoding encodingBoolBool
    (fun p => decide (p.1 < p.2)) :=
  prepareArithmeticComputes.andThen encodedComparisonComputes

noncomputable def subtractComputes : Computes natPairEncoding encodingNatBool
    (fun p => p.1 - p.2) :=
  prepareArithmeticComputes.andThen encodedSubtractionComputes

noncomputable def equalComputes : Computes natPairEncoding encodingBoolBool
    (fun p => decide (p.1 = p.2)) :=
  recode WordCompare.computes (fun p => (encodingNatBool.encode p.1,encodingNatBool.encode p.2))
    (fun _ => rfl) (fun p => by
      simp [WordCompare.value, encodingNatBool.encode_injective.eq_iff])

noncomputable def boolNatComputes : Computes encodingBoolBool encodingNatBool Bool.toNat :=
  FiniteRecode.computes encodingBoolBool encodingNatBool Bool.toNat 1 (fun b => by cases b <;> decide)

/-- A single physical pop computes truncated unary predecessor. -/
abbrev unaryPredecessorMachine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  program _ := .pop () (fun _ _ => ()) .halt

noncomputable def unaryPredecessorComputes :
    Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun n => n-1) where
  machine := unaryPredecessorMachine
  time := 1
  outputs n := {
    steps := 1
    evals_in_steps := by
      change unaryPredecessorMachine.computer.step
        (initList unaryPredecessorMachine.computer (UnaryBinary.unaryEncoding.encode n)) =
        some (haltList unaryPredecessorMachine.computer (UnaryBinary.unaryEncoding.encode (n-1)))
      cases n <;> simp [initList,haltList,UnaryBinary.unaryEncoding,
        unaryPredecessorMachine,FinTM2.step,TM2.step,TM2.stepAux,List.replicate_succ]
      funext k
      cases k
      simp
    steps_le_m := by simp }

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Endpoints

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WireLists

open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing StackProtocol
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
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
  congrComputes (UnaryRange.computes.andThen
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
  let chunks := Bytecode.flatMap (framedListEncoding e) _ (entriesComputes e)
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
  (pairComputes (identityComputes ea) (count.andThen UnaryRange.computes)).andThen
    (mapListComputes ea UnaryBinary.unaryEncoding eb f cell)

theorem lookup_primitive (e : Encoding A Bool) (default : A) (x : List A × ℕ) :
    let w := getD e default
    primitiveCost w.machine (w.outputs x).steps
      (some (initList w.machine.computer ((lookupEncoding e).encode x))) ≤
        (primitivePolynomial w).eval ((lookupEncoding e).encode x).length :=
  computes_primitive_cost (getD e default) x

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WireLists

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.AccessPrograms

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler

variable {A B C : Type} {ea : Encoding A Bool}

noncomputable def boolPairComputes (f : Bool × Bool → Bool) :
    Computes (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool f :=
  FiniteRecode.computes _ _ f 4 (fun x => by rcases x with ⟨a,b⟩; cases a <;> cases b <;> decide)


noncomputable def get (eb : Encoding B Bool) (d : B) {xs : A → List B} {i : A → ℕ}
    (list : Computes ea (framedListEncoding eb) xs) (index : Computes ea UnaryBinary.unaryEncoding i) :
    Computes ea eb (fun a => (xs a).getD (i a) d) :=
  (pairComputes list index).andThen (WireLists.getD eb d)

noncomputable def eqNat {f g : A → ℕ} (wf : Computes ea encodingNatBool f) (wg : Computes ea encodingNatBool g) :
    Computes ea encodingBoolBool (fun a => decide (f a = g a)) :=
  (pairComputes wf wg).andThen Endpoints.equalComputes

noncomputable def bool {f g : A → Bool} (op : Bool → Bool → Bool)
    (wf : Computes ea encodingBoolBool f) (wg : Computes ea encodingBoolBool g) :
    Computes ea encodingBoolBool (fun a => op (f a) (g a)) :=
  (pairComputes wf wg).andThen (boolPairComputes (fun p => op p.1 p.2))

noncomputable def flatMap (eb : Encoding B Bool) (ec : Encoding C Bool) (f : B → List C)
    (w : Computes eb (framedListEncoding ec) f) :
    Computes (framedListEncoding eb) (framedListEncoding ec) (List.flatMap f) :=
  congrComputes ((WireLists.mapComputes eb (framedListEncoding ec) f w).andThen (WireLists.flatten ec))
    (fun xs => by simp [List.flatMap_def])

noncomputable def map {xs : A → List B} (eb : Encoding B Bool) (ec : Encoding C Bool)
    (list : Computes ea (framedListEncoding eb) xs) (f : A → B → C)
    (cell : Computes (pairEncoding ea eb) ec (fun x => f x.1 x.2)) :
    Computes ea (framedListEncoding ec) (fun a => (xs a).map (f a)) :=
  (pairComputes (identityComputes ea) list).andThen (mapListComputes ea eb ec f cell)

noncomputable def unaryAdd : Computes (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
    UnaryBinary.unaryEncoding (fun x => x.1 + x.2) :=
  recode (joinComputes
    ((Wiring.firstComputes _ _).andThen (encodeComputes UnaryBinary.unaryEncoding))
    ((Wiring.secondComputes _ _).andThen (encodeComputes UnaryBinary.unaryEncoding))) id (fun _ => rfl)
    (fun x => by
      change List.replicate x.1 true ++ List.replicate x.2 true = List.replicate (x.1+x.2) true
      exact (List.replicate_add _ _ _).symm)

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.AccessPrograms

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
noncomputable def unaryEqual : Computes (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
    encodingBoolBool (fun p => decide (p.1 = p.2)) := equalComputes UnaryBinary.unaryEncoding
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.ResidueCells
open Computability Holant.Complexity BinaryCompose FixedFieldMachines
noncomputable def all : Computes (framedListEncoding encodingBoolBool) encodingBoolBool
    (fun xs => xs.all id) := by
  have h (xs : List Bool) (b : Bool) : xs.foldl Bool.and b = (b && xs.all id) := by
    induction xs generalizing b with
    | nil => cases b <;> rfl
    | cons x xs ih => simp only [List.foldl_cons, List.all_cons, ih]; cases b <;> cases x <;> simp
  exact congrComputes (FiniteFold.computes encodingBoolBool encodingBoolBool 1 Bool.and true
    (fun b => by cases b <;> rfl)) (fun xs => by simpa using h xs true)

noncomputable def any : Computes (framedListEncoding encodingBoolBool) encodingBoolBool
    (fun xs => xs.any id) := by
  have h (xs : List Bool) (b : Bool) : xs.foldl Bool.or b = (b || xs.any id) := by
    induction xs generalizing b with
    | nil => cases b <;> rfl
    | cons x xs ih => simp only [List.foldl_cons, List.any_cons, ih]; cases b <;> cases x <;> simp
  exact congrComputes (FiniteFold.computes encodingBoolBool encodingBoolBool 1 Bool.or false
    (fun b => by cases b <;> rfl)) (fun xs => by simpa using h xs false)


end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.ResidueCells
