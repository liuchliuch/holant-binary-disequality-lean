import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Layout

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Four literal live-reference array routers. The old array must already include
the emitted block's shift; this file does no gate emission. Default reads are
implemented physically, including the unused arm of each eager conditional.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Routing


open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler BitLayout Support.Combinators
open scoped Classical

abbrev Input := ℕ × (List ℕ × List ℕ)
abbrev Query := Input × ℕ
abbrev envEncoding := Environment.encoding
def inputEncoding := pairEncoding Unary.encoding (pairEncoding envEncoding envEncoding)
def queryEncoding := pairEncoding inputEncoding Unary.encoding

def capacityComputes : Computes inputEncoding Unary.encoding (fun p => p.1) :=
  Wiring.firstComputes _ _
def oldComputes : Computes inputEncoding envEncoding (fun p => p.2.1) :=
  (Wiring.secondComputes _ _).andThen (Wiring.firstComputes _ _)
def newComputes : Computes inputEncoding envEncoding (fun p => p.2.2) :=
  (Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _)
def contextComputes : Computes queryEncoding inputEncoding Prod.fst := Wiring.firstComputes _ _
def indexComputes : Computes queryEncoding Unary.encoding Prod.snd := Wiring.secondComputes _ _

def oldFixedComputes (i : ℕ) : Computes inputEncoding encodingNatBool (fun p => p.2.1.getD i 0) :=
  oldComputes.andThen (FixedGadgetSubstitution.Compiler.getDComputes encodingNatBool i 0)
def newFixedComputes (i : ℕ) : Computes inputEncoding encodingNatBool (fun p => p.2.2.getD i 0) :=
  newComputes.andThen (FixedGadgetSubstitution.Compiler.getDComputes encodingNatBool i 0)

variable (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]

def oldLabel (p : Input) (l : Option tm.Λ) := p.2.1.getD (Layout.rank l) 0
def oldState (p : Input) (s : tm.σ) := p.2.1.getD (Layout.stateIndex tm s) 0
def oldCell (p : Input) (k : tm.K) (i : ℕ) (a : Option (tm.Γ k)) :=
  p.2.1.getD (Layout.cellIndex tm p.1 k i a) 0

def cellReadComputes (k : tm.K) (a : Option (tm.Γ k)) (f : Query → ℕ)
    (wi : Computes queryEncoding Unary.encoding f) :
    Computes queryEncoding encodingNatBool (fun q => oldCell tm q.1 k (f q) a) :=
  (pairComputes (contextComputes.andThen oldComputes)
    ((pairComputes (contextComputes.andThen capacityComputes) wi).andThen
      (Layout.cellIndexComputes tm k a))).andThen (ListAccess.getDComputes encodingNatBool 0)

def label (p : Input) : List ℕ :=
  Layout.values tm p.1 (fun l => p.2.2.getD (Layout.rank l) 0) (oldState tm p) (oldCell tm p)
def state (p : Input) : List ℕ :=
  Layout.values tm p.1 (oldLabel tm p) (fun s => p.2.2.getD (Layout.rank s) 0) (oldCell tm p)

def labelComputes : Computes inputEncoding envEncoding (label tm) :=
  Layout.tabulateComputes tm inputEncoding encodingNatBool Prod.fst capacityComputes
    (fun p l => p.2.2.getD (Layout.rank l) 0) (oldState tm) (oldCell tm)
    (fun l => newFixedComputes (Layout.rank l))
    (fun s => oldFixedComputes (Layout.stateIndex tm s))
    (fun k a => cellReadComputes tm k a Prod.snd indexComputes)

def stateComputes : Computes inputEncoding envEncoding (state tm) :=
  Layout.tabulateComputes tm inputEncoding encodingNatBool Prod.fst capacityComputes
    (oldLabel tm) (fun p s => p.2.2.getD (Layout.rank s) 0) (oldCell tm)
    (fun l => oldFixedComputes (Layout.rank l))
    (fun s => newFixedComputes (Layout.rank s))
    (fun k a => cellReadComputes tm k a Prod.snd indexComputes)

def pushCell (k : tm.K) (p : Input) (j : tm.K) (i : ℕ) (a : Option (tm.Γ j)) : ℕ :=
  if h : j = k then
    if i = 0 then p.2.2.getD (Layout.rank (h ▸ a)) 0
    else oldCell tm p j (i - 1) a
  else oldCell tm p j i a

def popCell (k : tm.K) (p : Input) (j : tm.K) (i : ℕ) (a : Option (tm.Γ j)) : ℕ :=
  if h : j = k then
    if i + 1 < p.1 + 1 then oldCell tm p j (i + 1) a
    else p.2.2.getD (Layout.rank (h ▸ a)) 0
  else oldCell tm p j i a

def push (k : tm.K) (p : Input) : List ℕ :=
  Layout.values tm p.1 (oldLabel tm p) (oldState tm p) (pushCell tm k p)
def pop (k : tm.K) (p : Input) : List ℕ :=
  Layout.values tm p.1 (oldLabel tm p) (oldState tm p) (popCell tm k p)

def pushCellComputes (k j : tm.K) (a : Option (tm.Γ j)) :
    Computes queryEncoding encodingNatBool (fun q => pushCell tm k q.1 j q.2 a) := by
  by_cases hj : j = k
  · subst j
    let test := (pairComputes indexComputes (constantComputes queryEncoding Unary.encoding 0)).andThen Unary.equalComputes
    let prev := (pairComputes indexComputes (constantComputes queryEncoding Unary.encoding 1)).andThen Unary.subtractComputes
    exact congrComputes (ifComputes test
      (contextComputes.andThen (newFixedComputes (Layout.rank a)))
      (cellReadComputes tm k a _ prev)) (fun q => by simp [pushCell])
  · exact congrComputes (cellReadComputes tm j a Prod.snd indexComputes)
      (fun q => by simp [pushCell, hj])

def popCellComputes (k j : tm.K) (a : Option (tm.Γ j)) :
    Computes queryEncoding encodingNatBool (fun q => popCell tm k q.1 j q.2 a) := by
  by_cases hj : j = k
  · subst j
    let next := indexComputes.andThen Unary.successorComputes
    let limit := (contextComputes.andThen capacityComputes).andThen Unary.successorComputes
    let test := (pairComputes next limit).andThen Unary.lessComputes
    exact congrComputes (ifComputes test (cellReadComputes tm k a _ next)
      (contextComputes.andThen (newFixedComputes (Layout.rank a))))
      (fun q => by simp [popCell])
  · exact congrComputes (cellReadComputes tm j a Prod.snd indexComputes)
      (fun q => by simp [popCell, hj])

def pushComputes (k : tm.K) : Computes inputEncoding envEncoding (push tm k) :=
  Layout.tabulateComputes tm inputEncoding encodingNatBool Prod.fst capacityComputes
    (oldLabel tm) (oldState tm) (pushCell tm k)
    (fun l => oldFixedComputes (Layout.rank l))
    (fun s => oldFixedComputes (Layout.stateIndex tm s)) (pushCellComputes tm k)

def popComputes (k : tm.K) : Computes inputEncoding envEncoding (pop tm k) :=
  Layout.tabulateComputes tm inputEncoding encodingNatBool Prod.fst capacityComputes
    (oldLabel tm) (oldState tm) (popCell tm k)
    (fun l => oldFixedComputes (Layout.rank l))
    (fun s => oldFixedComputes (Layout.stateIndex tm s)) (popCellComputes tm k)

def input {O : Type} [Fintype O] (C : ℕ) (old : Address tm C → ℕ) (fresh : O → ℕ) : Input :=
  (C, (addresses tm C).map old, (fixedEnum O).map fresh)

theorem label_eq (C : ℕ) (old : Address tm C → ℕ) (fresh : Option tm.Λ → ℕ) :
    label tm (input tm C old fresh) = (addresses tm C).map
      (fun a => Sum.elim old fresh (PrimitiveBlocks.labelOutput tm C a)) := by
  rw [label, Layout.values_pack]
  apply List.map_congr_left
  intro a _
  rcases a with l | s | ⟨k, i, b⟩
  · exact Layout.read_fixed fresh l 0
  · exact Layout.read_state tm C old s 0
  · exact Layout.read_cell tm C old k i b 0

theorem state_eq (C : ℕ) (old : Address tm C → ℕ) (fresh : tm.σ → ℕ) :
    state tm (input tm C old fresh) = (addresses tm C).map
      (fun a => Sum.elim old fresh (PrimitiveBlocks.stateOutput tm C a)) := by
  rw [state, Layout.values_pack]
  apply List.map_congr_left
  intro a _
  rcases a with l | s | ⟨k, i, b⟩
  · exact Layout.read_label tm C old l 0
  · exact Layout.read_fixed fresh s 0
  · exact Layout.read_cell tm C old k i b 0

theorem push_eq (C : ℕ) (k : tm.K) (old : Address tm C → ℕ) (fresh : Option (tm.Γ k) → ℕ) :
    push tm k (input tm C old fresh) = (addresses tm C).map
      (fun a => Sum.elim old fresh (PrimitiveBlocks.pushOutput tm C k a)) := by
  rw [push, Layout.values_pack]
  apply List.map_congr_left
  intro a _
  rcases a with l | s | ⟨j, i, b⟩
  · exact Layout.read_label tm C old l 0
  · exact Layout.read_state tm C old s 0
  · by_cases hj : j = k
    · subst j
      by_cases hi : i.val = 0
      · simpa [pushCell, input, PrimitiveBlocks.pushOutput, hi] using Layout.read_fixed fresh b 0
      · simpa [pushCell, input, PrimitiveBlocks.pushOutput, hi, oldCell] using
          Layout.read_cell tm C old k ⟨i.val - 1, by
            have h := i.isLt
            change i.val < C + 1 at h
            omega⟩ b 0
    · simpa [pushCell, input, PrimitiveBlocks.pushOutput, hj, oldCell] using
        Layout.read_cell tm C old j i b 0

theorem pop_eq (C : ℕ) (k : tm.K) (old : Address tm C → ℕ) (fresh : Option (tm.Γ k) → ℕ) :
    pop tm k (input tm C old fresh) = (addresses tm C).map
      (fun a => Sum.elim old fresh (PrimitiveBlocks.popOutput tm C k a)) := by
  rw [pop, Layout.values_pack]
  apply List.map_congr_left
  intro a _
  rcases a with l | s | ⟨j, i, b⟩
  · exact Layout.read_label tm C old l 0
  · exact Layout.read_state tm C old s 0
  · by_cases hj : j = k
    · subst j
      by_cases hi : i.val + 1 < C + 1
      · simpa [popCell, input, PrimitiveBlocks.popOutput, hi, oldCell] using
          Layout.read_cell tm C old k ⟨i.val + 1, hi⟩ b 0
      · simpa [popCell, input, PrimitiveBlocks.popOutput, hi] using Layout.read_fixed fresh b 0
    · simpa [popCell, input, PrimitiveBlocks.popOutput, hj, oldCell] using
        Layout.read_cell tm C old j i b 0

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.Routing
