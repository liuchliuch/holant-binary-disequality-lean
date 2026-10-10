import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentRowSelectInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordJoin
import Holant.Complexity.FixedFieldMachines.Constant
import Holant.Complexity.GraphPreprocessing.UnaryBinary
import Mathlib.Data.List.GetD

/-! Literal list-building combinators for fixed-gadget compilation. The fixed
lists below compile to finite compositions. Unbounded input lists are traversed
by the proved Boolean-stack loop; no list callback is a machine operation. -/
namespace Holant.Complexity.FixedGadgetSubstitution.Compiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {A B C : Type}
def entry (e : Encoding B Bool) (b : B) : List Bool := true :: Holant.Algebraic.frame (e.encode b)
def entries (e : Encoding B Bool) (bs : List B) : List Bool := bs.flatMap (entry e)
noncomputable def encodeComputes (e : Encoding B Bool) :
    Computes e Frame.wordEncoding e.encode :=
  recode (identityComputes e) id (fun _ => rfl) (fun _ => rfl)
noncomputable def joinComputes {ea : Encoding A Bool} {f g : A → List Bool}
    (u : Computes ea Frame.wordEncoding f) (v : Computes ea Frame.wordEncoding g) :
    Computes ea Frame.wordEncoding (fun x => f x ++ g x) :=
  (pairComputes u v).andThen WordJoin.computes
noncomputable def frameComputes : Computes Frame.wordEncoding Frame.wordEncoding Holant.Algebraic.frame :=
  recode (pairComputes (identityComputes Frame.wordEncoding)
    (constantComputes Frame.wordEncoding Frame.wordEncoding [])) id (fun _ => rfl)
      (fun _ => by simp [pairEncoding, Frame.wordEncoding])
noncomputable def entryComputes (e : Encoding B Bool) : Computes e Frame.wordEncoding (entry e) :=
  congrComputes (joinComputes (constantComputes e Frame.wordEncoding [true])
    ((encodeComputes e).andThen frameComputes)) (fun _ => rfl)
/-- Finite compile-time concatenation, with each output supplied by real code. -/
noncomputable def fixedConcatComputes (ea : Encoding A Bool) (f : A → C → List Bool)
    (w : ∀ c, Computes ea Frame.wordEncoding (fun a => f a c)) :
    (xs : List C) → Computes ea Frame.wordEncoding (fun a => xs.flatMap (f a))
  | [] => constantComputes ea Frame.wordEncoding []
  | c :: cs => joinComputes (w c) (fixedConcatComputes ea f w cs)
theorem entries_append_encode (e : Encoding B Bool) (xs ys : List B) :
    entries e xs ++ framedListEncode e ys = framedListEncode e (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [entries,List.flatMap_cons,entry,List.cons_append,List.append_assoc,
      List.cons_append,framedListEncode] using congrArg (fun tail => entry e x ++ tail) ih
/-- A fixed list of computed values retains every element frame and terminator. -/
noncomputable def fixedListComputes (ea : Encoding A Bool) (eb : Encoding B Bool)
    (f : A → C → B) (w : ∀ c, Computes ea eb (fun a => f a c)) (xs : List C) :
    Computes ea (framedListEncoding eb) (fun a => xs.map (f a)) :=
  recode (joinComputes (fixedConcatComputes ea (fun a c => entry eb (f a c))
    (fun c => (w c).andThen (entryComputes eb)) xs)
      (constantComputes ea Frame.wordEncoding [false])) id (fun _ => rfl)
    (fun a => by
      have h := entries_append_encode eb (xs.map (f a)) []
      simpa only [entries,List.flatMap_map,Function.comp_def,List.append_nil,framedListEncode,
        Frame.wordEncoding,framedListEncoding,id_eq] using h)
noncomputable def entriesComputes (e : Encoding B Bool) :
    Computes (framedListEncoding e) Frame.wordEncoding (entries e) := by
  let provider : Computes (sigmaEncoding Frame.wordEncoding (fun _ => e)) Frame.wordEncoding
      (fun x => entry e x.2) :=
    recode ((Wiring.secondComputes Frame.wordEncoding e).andThen (entryComputes e))
      (fun x => (x.1,x.2)) (fun _ => rfl) (fun _ => rfl)
  let prepare : Computes (framedListEncoding e)
      (ContextFlatMap.inputEncoding Frame.wordEncoding (fun _ => e))
      (fun xs => (⟨[],xs⟩ : Σ _ : List Bool, List B)) :=
    recode (pairComputes (constantComputes (framedListEncoding e) Frame.wordEncoding [])
      (identityComputes (framedListEncoding e))) id (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ContextFlatMap.computes Frame.wordEncoding (fun _ => e) _ provider)
/-- Append a fixed suffix by reading and re-emitting every input record. -/
noncomputable def appendComputes (e : Encoding B Bool) (suffix : List B) :
    Computes (framedListEncoding e) (framedListEncoding e) (fun xs => xs ++ suffix) :=
  recode (joinComputes (entriesComputes e)
    (constantComputes (framedListEncoding e) Frame.wordEncoding (framedListEncode e suffix)))
      id (fun _ => rfl) (fun xs => entries_append_encode e xs suffix)
def paddedIndex (xs : List B) (i : ℕ) (d : B) : Fin (xs ++ List.replicate (i+1) d).length :=
  ⟨i, by simp only [List.length_append,List.length_replicate]; omega⟩
theorem padded_get (xs : List B) (i : ℕ) (d : B) :
    (xs ++ List.replicate (i+1) d).get (paddedIndex xs i d) = xs.getD i d := by
  change (xs ++ List.replicate (i+1) d)[i] = xs.getD i d
  by_cases h : i < xs.length
  · rw [List.getElem_append_left h, List.getD_eq_getElem xs d h]
  · rw [List.getElem_append_right (by omega)]
    rw [List.getD_eq_default xs d (by omega : xs.length ≤ i)]
    simp
/-- Total fixed-slot access implements Raw's exact getD convention. Padding is
physically emitted by finite code; the slot is then selected by ListIndex. -/
noncomputable def getDComputes (e : Encoding B Bool) (i : ℕ) (d : B) :
    Computes (framedListEncoding e) e (fun xs => xs.getD i d) := by
  let prepare : Computes (framedListEncoding e) (ParentRowSelect.inputEncoding e)
      (fun xs => ⟨xs ++ List.replicate (i+1) d,paddedIndex xs i d⟩) :=
    recode (pairComputes (appendComputes e (List.replicate (i+1) d))
      (constantComputes (framedListEncoding e) UnaryBinary.unaryEncoding i)) id
      (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen (ParentRowSelect.computes e)) (fun xs => padded_get xs i d)
end Holant.Complexity.FixedGadgetSubstitution.Compiler
