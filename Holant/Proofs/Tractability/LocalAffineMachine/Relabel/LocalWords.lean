import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.Catalogue
import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.FiniteDispatch


open Holant.Tractable.AffinePhase

namespace Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.LocalWords

open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler ProductMachine

def fixedEncoding (n : ℕ) : Encoding (Word n) Bool where
  encode x := WordLookup.wordEncoding.encode (List.ofFn x)
  decode bits := do
    let xs ← WordLookup.wordEncoding.decode bits
    if xs.length = n then some (fun j => xs.getD j.val false) else none
  decode_encode x := by simp [AffineMachine.DensePrograms.getD_ofFn]

theorem fixed_length (n : ℕ) (x : Word n) : (fixedEncoding n |>.encode x).length = 4 * n + 1 := by
  simp [fixedEncoding, WordLookup.word_length]

def portsEncoding := framedListEncoding RawClosedNetwork.endpointEncoding
def inputEncoding := pairEncoding WordLookup.wordEncoding portsEncoding
def sample (n : ℕ) (x : List Bool × List RawEndpoint) : Word n :=
  fun j => x.1.getD (Endpoint.number (x.2.getD j.val (0, false))) false

noncomputable def sampleComputes (n : ℕ) : Computes inputEncoding (fixedEncoding n) (sample n) := by
  let word := Wiring.firstComputes WordLookup.wordEncoding portsEncoding
  let ports := Wiring.secondComputes WordLookup.wordEncoding portsEncoding
  let bit (j : Fin n) := (pairComputes word
    ((ports.andThen (getDComputes RawClosedNetwork.endpointEncoding j.val (0, false))).andThen Endpoint.computes)).andThen
      WordLookup.computes
  refine recode (fixedListComputes inputEncoding encodingBoolBool (fun x j => sample n x j)
    bit (List.finRange n)) id (fun _ => rfl) ?_
  intro x
  simp [fixedEncoding, WordLookup.wordEncoding, List.ofFn_eq_map]

def edgeEncoding := pairEncoding WordLookup.wordEncoding encodingNatBool
def edgeSample (x : List Bool × ℕ) : Word 2 :=
  fun j => x.1.getD (Endpoint.number (x.2, j == 1)) false

noncomputable def edgeComputes : Computes edgeEncoding (fixedEncoding 2) edgeSample := by
  let word := Wiring.firstComputes WordLookup.wordEncoding encodingNatBool
  let e := Wiring.secondComputes WordLookup.wordEncoding encodingNatBool
  let endpoint (j : Fin 2) : Computes edgeEncoding RawClosedNetwork.endpointEncoding
      (fun x => (x.2, j == 1)) :=
    recode (pairComputes e (constantComputes edgeEncoding encodingBoolBool (j == 1)))
      id (fun _ => rfl) (fun _ => rfl)
  let bit (j : Fin 2) := (pairComputes word ((endpoint j).andThen Endpoint.computes)).andThen WordLookup.computes
  refine recode (fixedListComputes edgeEncoding encodingBoolBool (fun x j => edgeSample x j)
    bit (List.finRange 2)) id (fun _ => rfl) ?_
  intro x
  change (WordLookup.wordEncoding.encode ((List.finRange 2).map (edgeSample x))) =
    WordLookup.wordEncoding.encode (List.ofFn (edgeSample x))
  rw [List.ofFn_eq_map]

end Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.LocalWords
