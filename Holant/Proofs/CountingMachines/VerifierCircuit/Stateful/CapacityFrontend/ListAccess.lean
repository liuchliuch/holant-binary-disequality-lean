import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Unary

set_option backward.isDefEq.respectTransparency false

/-!
Ported reference proof. See the task validation reports.

Total runtime-indexed array access. Both the array and unary index are input
data. Padding, append, framing and selection are actual existing tape programs.
The machine's finite control is independent of the index and array length.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.ListAccess


open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler

variable {A B : Type}

def appendComputes (e : Encoding B Bool) :
    Computes (pairEncoding (framedListEncoding e) (framedListEncoding e))
      (framedListEncoding e) (fun p => p.1 ++ p.2) :=
  recode (joinComputes
    ((Wiring.firstComputes (framedListEncoding e) (framedListEncoding e)).andThen (entriesComputes e))
    ((Wiring.secondComputes (framedListEncoding e) (framedListEncoding e)).andThen
      (encodeComputes (framedListEncoding e)))) id (fun _ => rfl)
      (fun p => entries_append_encode e p.1 p.2)

def replicateComputes (e : Encoding B Bool) (d : B) :
    Computes Unary.encoding (framedListEncoding e) (fun n => List.replicate n d) := by
  let run := Support.WordLoops.repeatWordsComputes Unary.encoding id
    (identityComputes Unary.encoding) (fun _ => entry e d)
    (constantComputes Unary.encoding Frame.wordEncoding (entry e d))
  refine recode (joinComputes run (constantComputes Unary.encoding Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro n
  have h := entries_append_encode e (List.replicate n d) []
  simpa [entries, List.flatMap_def, Frame.wordEncoding, framedListEncoding, framedListEncode] using h

def inputEncoding (e : Encoding B Bool) := pairEncoding (framedListEncoding e) Unary.encoding

def getDComputes (e : Encoding B Bool) (d : B) :
    Computes (inputEncoding e) e (fun p => p.1.getD p.2 d) := by
  let array := Wiring.firstComputes (framedListEncoding e) Unary.encoding
  let index := Wiring.secondComputes (framedListEncoding e) Unary.encoding
  let padding := (index.andThen Unary.successorComputes).andThen (replicateComputes e d)
  let padded := (pairComputes array padding).andThen (appendComputes e)
  let prepare : Computes (inputEncoding e) (ParentRowSelect.inputEncoding e)
      (fun p => ⟨p.1 ++ List.replicate (p.2 + 1) d, paddedIndex p.1 p.2 d⟩) :=
    recode (pairComputes padded index) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen (ParentRowSelect.computes e))
    (fun p => padded_get p.1 p.2 d)

/-- Runtime-length tabulation; the provider is a proved finite tape program.
This is used for lists of live references, never for a host-side oracle. -/
def rangeComputes (ea : Encoding A Bool) (eb : Encoding B Bool)
    (n : A → ℕ) (count : Computes ea Unary.encoding n)
    (f : A × ℕ → B) (provider : Computes (pairEncoding ea Unary.encoding) eb f) :
    Computes ea (framedListEncoding eb) (fun x => (List.range (n x)).map (fun i => f (x, i))) := by
  let run := Support.WordLoops.rangeWordsComputes ea n count
    (fun x => entry eb (f x)) (provider.andThen (entryComputes eb))
  refine recode (joinComputes run (constantComputes ea Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro x
  have h := entries_append_encode eb ((List.range (n x)).map (fun i => f (x, i))) []
  simpa [entries, List.flatMap_map, Function.comp_def, Frame.wordEncoding,
    framedListEncoding, framedListEncode] using h

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.ListAccess
