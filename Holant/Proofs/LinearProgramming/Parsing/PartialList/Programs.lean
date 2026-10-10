import Holant.Proofs.LinearProgramming.Parsing.PartialList.Codec
import Holant.Proofs.LinearProgramming.Parsing.Pair

/-! Reuse the existing finite ContextFlatMap controller.
Each physical input frame calls the supplied actual component machine once.
Successful elements emit the original entry frame. Failed elements emit a
fixed malformed working word [false,true]; the existing Structural machine
then detects its premature terminator and clears every scratch/input stack.
The working sentinel is neither an A value nor an output protocol. AllSome
is only the proved specification of this finite composition. -/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.PartialList
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient
open Holant.Complexity.FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding sigmaEncoding)
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Factory
variable {A : Type} (ea : Encoding A Bool)
variable (w : Computes Frame.wordEncoding (optionEncoding ea) ea.decode)

def chunkComputes : Computes (optionEncoding ea) Frame.wordEncoding (chunk ea) :=
  congrComputes ((OptionMap.computes (entryComputes ea)).andThen
    (OptionalValue.getDComputes Frame.wordEncoding [false,true]))
      (fun q => by cases q <;> rfl)

/-- Existing provider invocation, on exactly frame(empty context) ++ raw element.
The old second-projection program physically strips that context frame. -/
def provider : Computes (sigmaEncoding Frame.wordEncoding (fun _ => Frame.wordEncoding))
    Frame.wordEncoding (fun p => chunk ea (ea.decode p.2)) :=
  recode ((Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding).andThen
    (w.andThen (chunkComputes ea))) (fun p => (p.1,p.2))
      (fun _ => rfl) (fun _ => rfl)

def prepare : Computes wordListEncoding
    (ContextFlatMap.inputEncoding Frame.wordEncoding (fun _ => Frame.wordEncoding))
    (fun xs => (⟨[],xs⟩ : Σ _ : List Bool, List (List Bool))) :=
  recode (pairComputes (constantComputes wordListEncoding Frame.wordEncoding [])
    (identityComputes wordListEncoding)) id (fun _ => rfl) (fun _ => rfl)

def traverse : Computes wordListEncoding Frame.wordEncoding
    (fun words => words.flatMap (fun word => chunk ea (ea.decode word))) :=
  congrComputes ((prepare).andThen
    (ContextFlatMap.computes Frame.wordEncoding (fun _ => Frame.wordEncoding) _ (provider ea w)))
      (fun _ => rfl)

def serialize : Computes wordListEncoding Frame.wordEncoding (emitted ea) :=
  congrComputes (joinComputes (traverse ea w)
    (constantComputes wordListEncoding Frame.wordEncoding [false])) (fun _ => rfl)

/-- The existing structural validator is the physical allSome failure branch.
It retains all successful original frames or returns a clean false-tag packet. -/
def semantic : Computes wordListEncoding (optionEncoding (framedListEncoding ea)) (allSome ea) :=
  recode ((serialize ea w).andThen Structural.WordList.computes) id
    (fun _ => rfl) (emitted_bytes ea)

/-- Generic constructor parameters are actual program objects and a pure
codec-image theorem. Parsing.Source.parseComputes installs its concrete
arguments internally and exposes no such parameter. -/
def computes (hs : Strict ea) :
    Computes Frame.wordEncoding (optionEncoding (framedListEncoding ea)) (framedListEncoding ea).decode := by
  let full := (Structural.WordList.computes.andThen (OptionMap.computes (semantic ea w))).andThen
    (OptionalValue.getDComputes (optionEncoding (framedListEncoding ea)) none)
  exact congrComputes full (fun input => by
    have old := decode_eq_old ea hs input
    change ((wordListEncoding.decode input).map (allSome ea)).getD none=
      (framedListEncoding ea).decode input
    rw [←old]
    unfold decode
    cases wordListEncoding.decode input <;> rfl)

/-- For every canonical input element, the original traversal executes exactly
the corresponding concrete provider receipt. This is an observer of the same
installed loop, not a new machine accepting per-element successful answers. -/
theorem traversal_exact (words : List (List Bool)) :
    StackProtocol.RunsExactly (ContextFlatMap.machine (provider ea w).machine).computer.step
      (initList (ContextFlatMap.machine (provider ea w).machine).computer
        (Holant.Algebraic.frame []++wordListEncoding.encode words))
      (haltList (ContextFlatMap.machine (provider ea w).machine).computer
        (words.flatMap (fun word => chunk ea (ea.decode word))))
      (ContextFlatMap.ticks Frame.wordEncoding []
        (fun word => chunk ea (ea.decode word))
        (fun word => ((provider ea w).outputs ⟨[],word⟩).steps) words+
        (words.flatMap (fun word => chunk ea (ea.decode word))).length+7) := by
  simpa only [wordListEncoding,Structural.WordList.encoding,framedListEncoding,List.length_nil,Nat.mul_zero,Nat.add_zero] using ContextFlatMap.whole
    (provider ea w).machine Frame.wordEncoding [] (fun word => chunk ea (ea.decode word))
    (fun word => ((provider ea w).outputs ⟨[],word⟩).steps) words
    (fun word _ => ((provider ea w).outputs ⟨[],word⟩).evals_in_steps)
end Factory

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.PartialList
