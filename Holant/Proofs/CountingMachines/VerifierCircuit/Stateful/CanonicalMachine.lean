import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.Bounds

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Physical canonical post-mux environment

Ported reference proof. See the task validation reports.

A descending unary-index traversal emits the actual binary register references
4*(D-1), ..., 0. The variable-width array is built on tapes at runtime.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CanonicalMachine


open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler BitLayout
open scoped Classical

abbrev unary := RuntimeParameters.unary
def values (D : ℕ) : List ℕ := (List.range D).reverse.map (fun i => 4 * i)

def indexEntryComputes : Computes (pairEncoding unary unary) Frame.wordEncoding
    (fun x => entry encodingNatBool (4 * x.2)) := by
  let binary := (Wiring.secondComputes unary unary).andThen UnaryBinary.computes
  let four := congrComputes ((binary.andThen doublingComputes).andThen doublingComputes)
    (fun x => by omega : ∀ x : ℕ × ℕ, 2 * (2 * x.2) = 4 * x.2)
  exact four.andThen (entryComputes encodingNatBool)

def computes : Computes unary Environment.encoding values := by
  let entries := Support.WordLoops.reverseRangeWordsComputes unary id
    (identityComputes unary) (fun x => entry encodingNatBool (4 * x.2)) indexEntryComputes
  refine recode (joinComputes entries (constantComputes unary Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro D
  have h := entries_append_encode encodingNatBool (values D) []
  simpa only [values, FixedGadgetSubstitution.Compiler.entries, List.flatMap_map, Function.comp_def,
    List.append_nil, id_eq,
    Environment.encoding, RuntimeRows.environmentEncoding, Frame.wordEncoding,
    framedListEncoding, framedListEncode] using h

@[simp] theorem values_length (D : ℕ) : (values D).length = D := by simp [values]

theorem get_value (D : ℕ) (i : Fin D) :
    (values D).get ⟨i.val, by simpa using i.isLt⟩ = 4 * (D - (i.val + 1)) := by
  simp [values, List.get_eq_getElem, List.getElem_reverse, Nat.sub_sub, Nat.add_comm]

theorem lookup_values {I : Type} [DecidableEq I] (layout : List I) (a : I) (ha : a ∈ layout) :
    Environment.lookup layout (values layout.length) a = 4 * (layout.length - (layout.idxOf a + 1)) := by
  have hi : layout.idxOf a < layout.length := List.idxOf_lt_length_iff.mpr ha
  unfold Environment.lookup
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  exact get_value layout.length ⟨layout.idxOf a, hi⟩

theorem lookup_reset (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)] (a : Address tm C) :
    Environment.lookup (addresses tm C) (values (addresses tm C).length) a = Reset.references tm C a :=
  lookup_values _ a (mem_addresses tm C a)

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CanonicalMachine
