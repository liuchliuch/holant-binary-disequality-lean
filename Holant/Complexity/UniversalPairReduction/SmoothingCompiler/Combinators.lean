import Holant.Complexity.FixedGadgetSubstitution.Compiler.Dispatch
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordCompare

/-! Concrete conditional and contextual list programs used by the pair smoother. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable {A B C : Type}
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

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
