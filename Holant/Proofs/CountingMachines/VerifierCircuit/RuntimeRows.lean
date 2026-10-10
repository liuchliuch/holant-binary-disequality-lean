import Holant.Proofs.CountingMachines.VerifierCircuit.RuntimeParameters
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Template

/-!
# Physical gate-record writers and live-register shifts

Ported reference proof. See the task validation reports.

All writers below output the existing `Circuit.rowEncoding`, including its
framing. They are concrete subroutines, not a `Computes` witness for the whole
verifier compiler. The stateful composition that tracks live contexts through
`Emit.parallel` and fixed-horizon iteration is still required.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeRows


open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler Support.Combinators

def operandsEncoding : Encoding (ℕ × ℕ) Bool := pairEncoding encodingNatBool encodingNatBool
def shiftOperandsEncoding : Encoding (ℕ × (ℕ × ℕ)) Bool := pairEncoding encodingNatBool operandsEncoding
def environmentEncoding : Encoding (List ℕ) Bool := framedListEncoding encodingNatBool

/-- After k new gates every retained register's de Bruijn index increases by k.
The traversal physically reads and writes each encoded register. -/
def shiftEnvironmentComputes :
    Computes (pairEncoding encodingNatBool environmentEncoding) environmentEncoding
      (fun p => p.2.map (fun i => p.1 + i)) :=
  mapListComputes encodingNatBool encodingNatBool encodingNatBool (fun k i => k + i) addComputes

def nandRowComputes : Computes operandsEncoding Circuit.rowEncoding (fun p => (2, p)) :=
  recode (pairComputes (constantComputes operandsEncoding encodingNatBool 2)
    (identityComputes operandsEncoding)) id (fun _ => rfl) (fun _ => rfl)

def constantRowComputes {A : Type} (e : Encoding A Bool) (b : Bool) :
    Computes e Circuit.rowEncoding (fun _ => (if b then 1 else 0, (0, 0))) :=
  constantComputes e Circuit.rowEncoding _

def nandEntryComputes : Computes operandsEncoding Frame.wordEncoding
    (fun p => entry Circuit.rowEncoding (2, p)) :=
  nandRowComputes.andThen (entryComputes Circuit.rowEncoding)

def constantEntryComputes {A : Type} (e : Encoding A Bool) (b : Bool) :
    Computes e Frame.wordEncoding (fun _ => entry Circuit.rowEncoding (if b then 1 else 0, (0, 0))) :=
  (constantRowComputes e b).andThen (entryComputes Circuit.rowEncoding)

def shiftOperandsComputes : Computes shiftOperandsEncoding operandsEncoding
    (fun p => (p.1 + p.2.1, p.1 + p.2.2)) := by
  let shift := Wiring.firstComputes encodingNatBool operandsEncoding
  let operands := Wiring.secondComputes encodingNatBool operandsEncoding
  let left := operands.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let right := operands.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  exact pairComputes ((pairComputes shift left).andThen addComputes)
    ((pairComputes shift right).andThen addComputes)

def shiftedNandEntryComputes : Computes shiftOperandsEncoding Frame.wordEncoding
    (fun p => entry Circuit.rowEncoding (2, (p.1 + p.2.1, p.1 + p.2.2))) :=
  shiftOperandsComputes.andThen nandEntryComputes

def slotBytes (W : ℕ) : List Bool :=
  framedListEncode encodingBoolBool (List.replicate W false)

/-- The old instance encoding charges an explicit slot for every witness,
including an unused witness. The loop emits those actual framed entries. -/
def slotBytesComputes : Computes RuntimeParameters.unary Frame.wordEncoding slotBytes := by
  let entriesMachine := Support.WordLoops.repeatWordsComputes
    RuntimeParameters.unary (fun n : ℕ => n) (identityComputes RuntimeParameters.unary)
    (fun _ => entry encodingBoolBool false)
    (constantComputes RuntimeParameters.unary Frame.wordEncoding (entry encodingBoolBool false))
  refine congrComputes (joinComputes entriesMachine
    (constantComputes RuntimeParameters.unary Frame.wordEncoding [false])) ?_
  intro n
  change (List.replicate n (entry encodingBoolBool false)).flatten ++ [false] = slotBytes n
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [List.replicate_succ, List.flatten_cons, List.append_assoc, slotBytes,
      framedListEncode, entry, List.cons_append] using
      congrArg (fun tail => entry encodingBoolBool false ++ tail) ih

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeRows
