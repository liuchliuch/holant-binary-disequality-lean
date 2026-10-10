import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators
import Holant.Complexity.GraphPreprocessing.ComponentSelection.UnaryRange
import Holant.Complexity.GraphPreprocessing.SignatureLabel
import Holant.Complexity.FixedFieldMachines.Reverse

/-! Physical Boolean-word loops for interpolation bytecode. All dynamic ranges
and repetitions use the existing finite contextual traversal machine. Descending
traversal reverses each emitted word and then reverses the concatenation. -/
namespace Holant.Complexity.BinaryInterpolation.WeightCompiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable {A : Type}
abbrev unary := UnaryBinary.unaryEncoding
abbrev labels := SignatureLabel.binaryFinEncoding 4

def chunk (c : Holant.OneHot.StackProgram.Code (Fin 4)) : List Bool :=
  entries (opEncoding labels) c

@[simp] theorem chunk_nil : chunk [] = [] := rfl
@[simp] theorem chunk_append (p q : Holant.OneHot.StackProgram.Code (Fin 4)) :
    chunk (p++q) = chunk p ++ chunk q := by simp [chunk,entries]

theorem chunk_flatMap {B : Type} (xs : List B) (f : B → Holant.OneHot.StackProgram.Code (Fin 4)) :
    chunk (xs.flatMap f) = xs.flatMap (fun x => chunk (f x)) := by
  simp [chunk,entries,List.flatMap_assoc]

noncomputable def reverseWordComputes : Computes Frame.wordEncoding Frame.wordEncoding List.reverse :=
  recode (reverseComputes Frame.wordEncoding) id (fun _ => rfl) (fun _ => rfl)

noncomputable def successorComputes : Computes unary unary (fun n => n+1) :=
  recode (joinComputes (identityComputes Frame.wordEncoding)
    (constantComputes Frame.wordEncoding Frame.wordEncoding [true]))
    (fun n => unary.encode n) (fun _ => rfl)
    (fun n => by simp [Frame.wordEncoding,unary,UnaryBinary.unaryEncoding,List.replicate_succ'])

/-- Enumerate the computed unary bound, then physically invoke the provider on
all encoded context/index pairs. -/
noncomputable def rangeWordsComputes (ea : Encoding A Bool) (n : A → ℕ)
    (count : Computes ea unary n) (f : A × ℕ → List Bool)
    (provider : Computes (pairEncoding ea unary) Frame.wordEncoding f) :
    Computes ea Frame.wordEncoding (fun x => (List.range (n x)).flatMap (fun i => f (x,i))) := by
  let prepare := pairComputes (identityComputes ea) (count.andThen ComponentSelection.UnaryRange.computes)
  let run : Computes (pairEncoding ea (framedListEncoding unary)) Frame.wordEncoding
      (fun x => x.2.flatMap (fun i => f (x.1,i))) :=
    recode (ContextFlatMap.computes ea (fun _ => unary) (fun x => f (x.1,x.2))
    (recode provider (fun x => (x.1,x.2)) (fun _ => rfl) (fun _ => rfl)))
    (fun x : A × List ℕ => ⟨x.1,x.2⟩) (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen run

noncomputable def reverseRangeWordsComputes (ea : Encoding A Bool) (n : A → ℕ)
    (count : Computes ea unary n) (f : A × ℕ → List Bool)
    (provider : Computes (pairEncoding ea unary) Frame.wordEncoding f) :
    Computes ea Frame.wordEncoding (fun x => (List.range (n x)).reverse.flatMap (fun i => f (x,i))) :=
  congrComputes ((rangeWordsComputes ea n count (fun x => (f x).reverse)
    (provider.andThen reverseWordComputes)).andThen reverseWordComputes)
    (fun x => by simp [List.reverse_flatMap,Function.comp_def])

noncomputable def repeatWordsComputes (ea : Encoding A Bool) (n : A → ℕ)
    (count : Computes ea unary n) (f : A → List Bool)
    (provider : Computes ea Frame.wordEncoding f) :
    Computes ea Frame.wordEncoding (fun x => (List.replicate (n x) (f x)).flatten) :=
  congrComputes (rangeWordsComputes ea n count (fun x => f x.1)
    ((Wiring.firstComputes ea unary).andThen provider)) (fun x => by simp [List.flatMap_def])

noncomputable def multiplyUnaryComputes :
    Computes (pairEncoding unary unary) unary (fun x => x.1*x.2) :=
  recode (repeatWordsComputes (pairEncoding unary unary) Prod.fst
    (Wiring.firstComputes unary unary) (fun x => unary.encode x.2)
    ((Wiring.secondComputes unary unary).andThen (encodeComputes unary)))
    id (fun _ => rfl) (fun x => by
      simp [Frame.wordEncoding,unary,UnaryBinary.unaryEncoding,List.flatten_replicate_replicate])

abbrev Emits (ea : Encoding A Bool) (f : A → Holant.OneHot.StackProgram.Code (Fin 4)) :=
  Computes ea Frame.wordEncoding (fun x => chunk (f x))

noncomputable def constantEmits (ea : Encoding A Bool) (c : Holant.OneHot.StackProgram.Code (Fin 4)) :
    Emits ea (fun _ => c) := constantComputes ea Frame.wordEncoding (chunk c)

noncomputable def appendEmits {ea : Encoding A Bool} {f g : A → Holant.OneHot.StackProgram.Code (Fin 4)}
    (a : Emits ea f) (b : Emits ea g) : Emits ea (fun x => f x ++ g x) :=
  congrComputes (joinComputes a b) (fun x => (chunk_append _ _).symm)

noncomputable def rangeEmits (ea : Encoding A Bool) (n : A → ℕ) (count : Computes ea unary n)
    (f : A × ℕ → Holant.OneHot.StackProgram.Code (Fin 4))
    (provider : Emits (pairEncoding ea unary) f) :
    Emits ea (fun x => (List.range (n x)).flatMap (fun i => f (x,i))) :=
  congrComputes (rangeWordsComputes ea n count (fun x => chunk (f x)) provider)
    (fun x => (chunk_flatMap _ _).symm)

noncomputable def reverseRangeEmits (ea : Encoding A Bool) (n : A → ℕ) (count : Computes ea unary n)
    (f : A × ℕ → Holant.OneHot.StackProgram.Code (Fin 4))
    (provider : Emits (pairEncoding ea unary) f) :
    Emits ea (fun x => (List.range (n x)).reverse.flatMap (fun i => f (x,i))) :=
  congrComputes (reverseRangeWordsComputes ea n count (fun x => chunk (f x)) provider)
    (fun x => (chunk_flatMap _ _).symm)

noncomputable def repeatEmits (ea : Encoding A Bool) (n : A → ℕ) (count : Computes ea unary n)
    (c : Holant.OneHot.StackProgram.Code (Fin 4)) :
    Emits ea (fun x => (List.replicate (n x) c).flatten) :=
  congrComputes (repeatWordsComputes ea n count (fun _ => chunk c) (constantEmits ea c))
    (fun x => by
      change (List.replicate (n x) (chunk c)).flatten = chunk ((List.replicate (n x) c).flatten)
      induction n x with
      | zero => rfl
      | succ k ih => simp only [List.replicate_succ,List.flatten_cons,chunk_append,ih])

end Holant.Complexity.BinaryInterpolation.WeightCompiler
