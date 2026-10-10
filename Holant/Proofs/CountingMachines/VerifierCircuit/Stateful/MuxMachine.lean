import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.Indexed
import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.OutputMachine

set_option backward.isDefEq.respectTransparency false

/-!
# Actual four-NAND mux and variable-width mux-bundle output machines

Ported reference proof. See the task validation reports.

The ith bundle entry is shifted by 4*i by actual binary arithmetic. The
index is obtained from the physical unary query index, not an unbounded state
register. `batch_eq_gather` identifies the resulting exact old Circuit rows.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.MuxMachine


open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler OutputMachine

abbrev Triple := ℕ × (ℕ × ℕ)
def tripleEncoding : Encoding Triple Bool :=
  pairEncoding encodingNatBool (pairEncoding encodingNatBool encodingNatBool)

def records (x : Triple) : List Circuit.Row :=
  [(2, (x.1, x.2.1)), (2, (x.1 + 1, x.1 + 1)), (2, (0, x.2.2 + 2)), (2, (2, 0))]

def bytes (x : Triple) : List Bool := rowBytes (records x)

def computes : Computes tripleEncoding Frame.wordEncoding bytes := by
  let s := Wiring.firstComputes encodingNatBool RuntimeRows.operandsEncoding
  let rest := Wiring.secondComputes encodingNatBool RuntimeRows.operandsEncoding
  let t := rest.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let e := rest.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  let s1 := (pairComputes s (constantComputes tripleEncoding encodingNatBool 1)).andThen addComputes
  let e2 := (pairComputes e (constantComputes tripleEncoding encodingNatBool 2)).andThen addComputes
  let first := (pairComputes s t).andThen RuntimeRows.nandEntryComputes
  let second := (pairComputes s1 s1).andThen RuntimeRows.nandEntryComputes
  let third := (pairComputes (constantComputes tripleEncoding encodingNatBool 0) e2).andThen RuntimeRows.nandEntryComputes
  let fourth := constantComputes tripleEncoding Frame.wordEncoding (entry Circuit.rowEncoding (2, (2, 0)))
  exact congrComputes (joinComputes first (joinComputes second (joinComputes third fourth)))
    (fun x => by simp [bytes, records, rowBytes, entries, entry, List.append_assoc])

def shiftTriple (g : ℕ) (x : Triple) : Triple := (x.1 + g, x.2.1 + g, x.2.2 + g)
def shiftEncoding := pairEncoding encodingNatBool tripleEncoding

def shiftComputes : Computes shiftEncoding tripleEncoding (fun x => shiftTriple x.1 x.2) := by
  let g := Wiring.firstComputes encodingNatBool tripleEncoding
  let triple := Wiring.secondComputes encodingNatBool tripleEncoding
  let s := triple.andThen (Wiring.firstComputes encodingNatBool RuntimeRows.operandsEncoding)
  let rest := triple.andThen (Wiring.secondComputes encodingNatBool RuntimeRows.operandsEncoding)
  let t := rest.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let e := rest.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  exact pairComputes ((pairComputes s g).andThen addComputes)
    (pairComputes ((pairComputes t g).andThen addComputes) ((pairComputes e g).andThen addComputes))

def fourIndexComputes : Computes (Indexed.queryEncoding tripleEncoding) encodingNatBool
    (fun x => 4 * x.2.val) :=
  congrComputes (((Indexed.indexComputes tripleEncoding).andThen doublingComputes).andThen doublingComputes)
    (fun x => by simp only [Function.comp_apply]; omega)

def providerComputes : Computes (Indexed.queryEncoding tripleEncoding) Frame.wordEncoding
    (fun x => bytes (shiftTriple (4 * x.2.val) (x.1.get x.2))) :=
  ((pairComputes fourIndexComputes (Indexed.selectedComputes tripleEncoding)).andThen shiftComputes).andThen computes

def batchRecords (xs : List Triple) : List Circuit.Row :=
  (List.ofFn (fun i : Fin xs.length => records (shiftTriple (4 * i.val) (xs.get i)))).flatten

def batchComputes : Computes (framedListEncoding tripleEncoding) Frame.wordEncoding
    (fun xs => rowBytes (batchRecords xs)) :=
  congrComputes (Indexed.wordsComputes tripleEncoding _ providerComputes) (fun xs => by
    simp [Indexed.words, batchRecords, rowBytes_flatten, List.map_ofFn, bytes, Function.comp_def])

theorem batch_eq_gather {I J : Type} (xs : List J) (s t e : J → I) (env : I → ℕ) :
    batchRecords (xs.map (fun j => (env (s j), env (t j), env (e j)))) =
      (Rows.gather (fun j => Rows.mux (s j) (t j) (e j)) xs env).1 := by
  rw [Indexed.gather_rows _ 4 (fun _ _ => Rows.mux_length _ _ _ _)]
  simp [batchRecords, records, shiftTriple, Rows.mux_rows, Rows.shift,
    List.get_eq_getElem, List.ofFn_eq_map, List.map_map, Function.comp_def]

theorem tabulate_rows {I J : Type} [DecidableEq J] (xs : List J) (covers : ∀ j, j ∈ xs)
    (s t e : J → I) (env : I → ℕ) :
    (Rows.tabulate xs covers (fun j => Rows.mux (s j) (t j) (e j)) env).1 =
      batchRecords (xs.map (fun j => (env (s j), env (t j), env (e j)))) := by
  simpa [Rows.tabulate, Rows.renameOutput, Rows.seq, Rows.route] using
    (batch_eq_gather xs s t e env).symm

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.MuxMachine
