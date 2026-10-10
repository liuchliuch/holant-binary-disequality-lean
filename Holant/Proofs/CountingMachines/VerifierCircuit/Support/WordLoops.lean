import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists
import Holant.Proofs.CountingMachines.VerifierCircuit.Support.Combinators
import Holant.Complexity.GraphPreprocessing.ComponentSelection.UnaryRange
import Holant.Complexity.FixedFieldMachines.Reverse

/-! Physical unary arithmetic and word loops, extracted from the reference compiler. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Support.WordLoops
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Support.Combinators
variable {A : Type}
abbrev unary := UnaryBinary.unaryEncoding

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

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Support.WordLoops
