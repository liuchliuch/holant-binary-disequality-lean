import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Routing
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitReadInterface

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Initial coordinates are selected from original input bits, witness positions,
or empty padding. A plan item is (witness?, unary witness index, true/false
constants). It is finite tape data, not an instruction with a semantic oracle.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.InitialPlan


open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open BitLayout Support.Combinators
open scoped Classical

abbrev Item := Bool × (ℕ × (Bool × Bool))
def itemEncoding := pairEncoding encodingBoolBool
  (pairEncoding Unary.encoding (pairEncoding encodingBoolBool encodingBoolBool))
def constant (b : Bool) : Item := (false, 0, b, b)
def witness (j : ℕ) (t e : Bool) : Item := (true, j, t, e)
def cost (p : Item) : ℕ := if p.1 then 6 else 1
def value (p : Item) (bits : ℕ → Bool) : Bool := if p.1 then if bits p.2.1 then p.2.2.1 else p.2.2.2 else p.2.2.1

def wordQueryEncoding := pairEncoding Frame.wordEncoding Unary.encoding

/-- Total original-bit access with literal runtime padding, never a decoder
operation. In the original-input region the returned bit is the real input bit. -/
def wordGetDComputes : Computes wordQueryEncoding encodingBoolBool
    (fun p => p.1.getD p.2 false) := by
  let word := Wiring.firstComputes Frame.wordEncoding Unary.encoding
  let index := Wiring.secondComputes Frame.wordEncoding Unary.encoding
  let padding := Support.WordLoops.repeatWordsComputes wordQueryEncoding
    (fun p => p.2 + 1) (index.andThen Unary.successorComputes) (fun _ => [false])
    (constantComputes wordQueryEncoding Frame.wordEncoding [false])
  let padded : Computes wordQueryEncoding Frame.wordEncoding
      (fun p => p.1 ++ List.replicate (p.2 + 1) false) :=
    congrComputes (joinComputes word padding) (fun p => by simp)
  let prepare : Computes wordQueryEncoding BitRead.inputEncoding
      (fun p => ⟨p.1 ++ List.replicate (p.2 + 1) false, paddedIndex p.1 p.2 false⟩) :=
    recode (pairComputes padded index) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen BitRead.computes) (fun p => padded_get p.1 p.2 false)

abbrev Input := List Bool × (ℕ × ℕ)
abbrev Query := Input × ℕ
def inputEncoding := pairEncoding Frame.wordEncoding (pairEncoding Unary.encoding Unary.encoding)
def queryEncoding := pairEncoding inputEncoding Unary.encoding
def wordComputes : Computes inputEncoding Frame.wordEncoding (fun p => p.1) := Wiring.firstComputes _ _
def witnessLengthComputes : Computes inputEncoding Unary.encoding (fun p => p.2.1) :=
  (Wiring.secondComputes _ _).andThen (Wiring.firstComputes _ _)
def capacityComputes : Computes inputEncoding Unary.encoding (fun p => p.2.2) :=
  (Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _)
def contextComputes : Computes queryEncoding inputEncoding Prod.fst := Wiring.firstComputes _ _
def indexComputes : Computes queryEncoding Unary.encoding Prod.snd := Wiring.secondComputes _ _

variable (tm : FinTM2) [∀ k, Fintype (tm.Γ k)] (e : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)

def inputCell (p : Input) (i : ℕ) (a : Option (tm.Γ tm.k₀)) : Item :=
  if i < p.1.length then constant (oneHot (some (e.symm (.inl (p.1.getD i false)))) a)
  else if i < p.1.length + p.2.1 then witness (i - p.1.length)
    (oneHot (some (e.symm (.inr true))) a) (oneHot (some (e.symm (.inr false))) a)
  else constant (oneHot (none : Option (tm.Γ tm.k₀)) a)

def cell (p : Input) (k : tm.K) (i : ℕ) (a : Option (tm.Γ k)) : Item :=
  if h : k = tm.k₀ then inputCell tm e p i (h ▸ a)
  else constant (oneHot (none : Option (tm.Γ k)) a)

def plan (p : Input) : List Item := Layout.values tm p.2.2
  (fun l => constant (oneHot (some tm.main) l))
  (fun s => constant (oneHot tm.initialState s)) (cell tm e p)

def constantItemComputes : Computes encodingBoolBool itemEncoding constant :=
  pairComputes (constantComputes _ encodingBoolBool false)
    (pairComputes (constantComputes _ Unary.encoding 0)
      (pairComputes (identityComputes encodingBoolBool) (identityComputes encodingBoolBool)))

def inputCellComputes (a : Option (tm.Γ tm.k₀)) :
    Computes queryEncoding itemEncoding (fun q => inputCell tm e q.1 q.2 a) := by
  let word := contextComputes.andThen wordComputes
  let len := word.andThen (RuntimeParameters.lengthComputes Frame.wordEncoding)
  let count := contextComputes.andThen witnessLengthComputes
  let last := (pairComputes len count).andThen Unary.addComputes
  let isInput := (pairComputes indexComputes len).andThen Unary.lessComputes
  let isWitness := (pairComputes indexComputes last).andThen Unary.lessComputes
  let bit := (pairComputes word indexComputes).andThen wordGetDComputes
  let inputValue := ifComputes bit
    (constantComputes queryEncoding encodingBoolBool
      (oneHot (some (e.symm (.inl true))) a))
    (constantComputes queryEncoding encodingBoolBool
      (oneHot (some (e.symm (.inl false))) a))
  let inputItem := inputValue.andThen constantItemComputes
  let witnessItem := pairComputes
    (constantComputes queryEncoding encodingBoolBool true)
    (pairComputes ((pairComputes indexComputes len).andThen Unary.subtractComputes)
      (constantComputes queryEncoding
        (pairEncoding encodingBoolBool encodingBoolBool)
        (oneHot (some (e.symm (.inr true))) a, oneHot (some (e.symm (.inr false))) a)))
  let emptyItem := constantComputes queryEncoding itemEncoding
    (constant (oneHot (none : Option (tm.Γ tm.k₀)) a))
  refine congrComputes (ifComputes isInput inputItem (ifComputes isWitness witnessItem emptyItem)) ?_
  intro q
  change _ = inputCell tm e q.1 q.2 a
  cases hb : q.1.1[q.2]?.getD false <;>
    simp [inputCell, constant, witness, Frame.wordEncoding, hb, List.getD]

def cellComputes (k : tm.K) (a : Option (tm.Γ k)) :
    Computes queryEncoding itemEncoding (fun q => cell tm e q.1 k q.2 a) := by
  by_cases hk : k = tm.k₀
  · subst k
    exact congrComputes (inputCellComputes tm e a) (fun q => by simp [cell])
  · exact congrComputes
      (constantComputes queryEncoding itemEncoding
        (constant (oneHot (none : Option (tm.Γ k)) a))) (fun q => by simp [cell, hk])

def computes : Computes inputEncoding (framedListEncoding itemEncoding) (plan tm e) :=
  Layout.tabulateComputes tm inputEncoding itemEncoding (fun p => p.2.2) capacityComputes
    (fun _ l => constant (oneHot (some tm.main) l))
    (fun _ s => constant (oneHot tm.initialState s)) (cell tm e)
    (fun l => constantComputes inputEncoding itemEncoding
      (constant (oneHot (some tm.main) l)))
    (fun s => constantComputes inputEncoding itemEncoding
      (constant (oneHot tm.initialState s))) (cellComputes tm e)

theorem plan_order (p : Input) : plan tm e p = (addresses tm p.2.2).map (fun a => match a with
    | .inl l => constant (oneHot (some tm.main) l)
    | .inr (.inl s) => constant (oneHot tm.initialState s)
    | .inr (.inr ⟨k, i, b⟩) => cell tm e p k i.val b) := by
  unfold plan
  convert Layout.values_pack tm p.2.2
    (fun l => constant (oneHot (some tm.main) l))
    (fun s => constant (oneHot tm.initialState s)) (cell tm e p) using 1 <;>
    congr 1
  funext a
  rcases a with l | s | ⟨k, i, b⟩ <;> rfl

theorem plan_length (p : Input) : (plan tm e p).length = (addresses tm p.2.2).length := by
  rw [plan_order, List.length_map]

theorem input_region (p : Input) (i : ℕ) (hi : i < p.1.length) (a : Option (tm.Γ tm.k₀)) :
    inputCell tm e p i a = constant (oneHot (some (e.symm (.inl p.1[i]))) a) := by
  simp [inputCell, hi, List.getD_eq_getElem _ _ hi]

theorem witness_region (p : Input) (i : ℕ) (hlo : p.1.length ≤ i)
    (hhi : i < p.1.length + p.2.1) (a : Option (tm.Γ tm.k₀)) :
    inputCell tm e p i a = witness (i - p.1.length)
      (oneHot (some (e.symm (.inr true))) a) (oneHot (some (e.symm (.inr false))) a) := by
  simp [inputCell, Nat.not_lt.mpr hlo, hhi]

theorem padding_region (p : Input) (i : ℕ) (hi : p.1.length + p.2.1 ≤ i)
    (a : Option (tm.Γ tm.k₀)) : inputCell tm e p i a = constant (oneHot none a) := by
  have hlo : p.1.length ≤ i := by omega
  simp [inputCell, Nat.not_lt.mpr hlo, Nat.not_lt.mpr hi]

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.InitialPlan
