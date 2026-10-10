import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.InitialPlan

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Physical initial-plan emission with runtime «prefix» and suffix gate sums. The
quadratic traversal is intentional: it uses existing proved list/word loops and
has a composed polynomial time bound, without a free accumulator instruction.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.PlanRows

open Holant.LocalDrafts.CountingHardness

open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler Support.Combinators
open InitialPlan OutputMachine

abbrev encoding := framedListEncoding itemEncoding
abbrev Query := List Item × ℕ
def queryEncoding := pairEncoding encoding Unary.encoding
def itemQueryEncoding := pairEncoding itemEncoding Unary.encoding
def defaultItem : Item := InitialPlan.constant false

def prefixCost (xs : List Item) (i : ℕ) : ℕ :=
  ((List.range i).map (fun j => cost (xs.getD j defaultItem))).sum

theorem prefix_eq_take (xs : List Item) (i : ℕ) (hi : i ≤ xs.length) :
    prefixCost xs i = ((xs.take i).map cost).sum := by
  have h : (List.range i).map (fun j => xs.getD j defaultItem) = xs.take i := by
    apply List.ext_getElem
    · simp [Nat.min_eq_left hi]
    · intro j hj hk
      have hji : j < i := by simpa using hj
      have hjx : j < xs.length := lt_of_lt_of_le hji hi
      simp [List.getElem?_eq_getElem hjx]
  rw [← h, List.map_map]
  rfl

def costComputes : Computes itemEncoding Unary.encoding cost :=
  ifComputes (Wiring.firstComputes _ _) (constantComputes itemEncoding Unary.encoding 6)
    (constantComputes itemEncoding Unary.encoding 1)

def arrayComputes : Computes queryEncoding encoding Prod.fst := Wiring.firstComputes _ _
def indexComputes : Computes queryEncoding Unary.encoding Prod.snd := Wiring.secondComputes _ _
def selectedComputes : Computes queryEncoding itemEncoding (fun q => q.1.getD q.2 defaultItem) :=
  ListAccess.getDComputes itemEncoding defaultItem

def prefixComputes : Computes queryEncoding Unary.encoding (fun q => prefixCost q.1 q.2) := by
  let context := Wiring.firstComputes queryEncoding Unary.encoding
  let index := Wiring.secondComputes queryEncoding Unary.encoding
  let selected := (pairComputes (context.andThen arrayComputes) index).andThen selectedComputes
  let provider := (selected.andThen costComputes).andThen (encodeComputes Unary.encoding)
  let run := Support.WordLoops.rangeWordsComputes queryEncoding Prod.snd indexComputes
    (fun q => Unary.encoding.encode (cost (q.1.1.getD q.2 defaultItem))) provider
  refine recode run id (fun _ => rfl) ?_
  intro q
  change (List.range q.2).flatMap (fun j => List.replicate (cost (q.1.getD j defaultItem)) true) =
    List.replicate (prefixCost q.1 q.2) true
  unfold prefixCost
  generalize List.range q.2 = js
  induction js with
  | nil => rfl
  | cons j js ih => simp only [List.flatMap_cons, List.map_cons, List.sum_cons, List.replicate_add, ih]

def countComputes : Computes encoding Unary.encoding List.length := Indexed.countComputes itemEncoding
def totalComputes : Computes encoding Unary.encoding (fun xs => prefixCost xs xs.length) :=
  (pairComputes (identityComputes encoding) countComputes).andThen prefixComputes

def suffixCost (xs : List Item) (i : ℕ) : ℕ := prefixCost xs xs.length - prefixCost xs (i + 1)

def suffixComputes : Computes queryEncoding Unary.encoding (fun q => suffixCost q.1 q.2) :=
  (pairComputes (arrayComputes.andThen totalComputes)
    ((pairComputes arrayComputes (indexComputes.andThen Unary.successorComputes)).andThen
      prefixComputes)).andThen Unary.subtractComputes

theorem suffix_eq_drop (xs : List Item) (i : ℕ) (hi : i < xs.length) :
    suffixCost xs i = ((xs.drop (i + 1)).map cost).sum := by
  rw [suffixCost, prefix_eq_take _ _ (Nat.le_refl _), prefix_eq_take _ _ (by omega)]
  simp only [List.take_length]
  have h := congrArg (fun ys : List Item => (ys.map cost).sum) (List.take_append_drop (i + 1) xs)
  simp only [List.map_append, List.sum_append] at h
  omega

def records (p : Item) (g : ℕ) : List Circuit.Row :=
  if p.1 then
    [(if p.2.2.1 then 1 else 0, (0, 0)), (if p.2.2.2 then 1 else 0, (0, 0))] ++
      MuxMachine.records (p.2.1 + g + 2, 1, 0)
  else [(if p.2.2.1 then 1 else 0, (0, 0))]

theorem records_length (p : Item) (g : ℕ) : (records p g).length = cost p := by
  cases h : p.1 <;> simp [records, cost, MuxMachine.records, h]

theorem constant_records (b : Bool) (g : ℕ) :
    records (InitialPlan.constant b) g = (Rows.constant (I := ℕ) b (Rows.shift g id)).1 := rfl

theorem witness_records (j : ℕ) (t e : Bool) (g : ℕ) :
    records (witness j t e) g =
      (InitialRows.boolMap j (fun b => if b then t else e) (Rows.shift g id)).1 := by
  simp [records, witness, MuxMachine.records, InitialRows.boolMap,
    Rows.seq, Rows.parallel, Rows.route, Rows.constant, Rows.mux, Rows.nand, Rows.not,
    Rows.shift, Nat.add_assoc]

def constantBytesComputes : Computes encodingBoolBool Frame.wordEncoding
    (fun b => rowBytes [(if b then 1 else 0, (0, 0))]) := by
  refine congrComputes (ifComputes (identityComputes encodingBoolBool)
    (RuntimeRows.constantEntryComputes encodingBoolBool true)
    (RuntimeRows.constantEntryComputes encodingBoolBool false)) ?_
  intro b
  cases b <;> rfl

def recordsComputes : Computes itemQueryEncoding Frame.wordEncoding (fun q => rowBytes (records q.1 q.2)) := by
  let item := Wiring.firstComputes itemEncoding Unary.encoding
  let offset := Wiring.secondComputes itemEncoding Unary.encoding
  let kind := item.andThen (Wiring.firstComputes _ _)
  let tail := item.andThen (Wiring.secondComputes _ _)
  let index := tail.andThen (Wiring.firstComputes _ _)
  let constants := tail.andThen (Wiring.secondComputes _ _)
  let yes := constants.andThen (Wiring.firstComputes encodingBoolBool encodingBoolBool)
  let no := constants.andThen (Wiring.secondComputes encodingBoolBool encodingBoolBool)
  let first := yes.andThen constantBytesComputes
  let second := no.andThen constantBytesComputes
  let shifted := ((pairComputes ((pairComputes index offset).andThen Unary.addComputes)
    (constantComputes itemQueryEncoding Unary.encoding 2)).andThen Unary.addComputes).andThen UnaryBinary.computes
  let mux := (pairComputes shifted (constantComputes itemQueryEncoding
    RuntimeRows.operandsEncoding (1, 0))).andThen MuxMachine.computes
  refine congrComputes (ifComputes kind (joinComputes first (joinComputes second mux)) first) ?_
  intro q
  cases h : q.1.1 <;>
    simp [records, h, rowBytes_append, rowBytes, entries, MuxMachine.bytes, List.append_assoc]

def blockComputes : Computes queryEncoding Frame.wordEncoding
    (fun q => rowBytes (records (q.1.getD q.2 defaultItem) (prefixCost q.1 q.2))) :=
  (pairComputes selectedComputes prefixComputes).andThen recordsComputes

def rows (xs : List Item) : List Circuit.Row :=
  (List.range xs.length).flatMap (fun i => records (xs.getD i defaultItem) (prefixCost xs i))
def references (xs : List Item) : List ℕ := (List.range xs.length).map (suffixCost xs)
def result (xs : List Item) : List Bool × List ℕ := (rowBytes (rows xs), references xs)
def resultEncoding := pairEncoding Frame.wordEncoding Environment.encoding

def rowsComputes : Computes encoding Frame.wordEncoding (fun xs => rowBytes (rows xs)) :=
  congrComputes (Support.WordLoops.rangeWordsComputes encoding List.length countComputes
    (fun q => rowBytes (records (q.1.getD q.2 defaultItem) (prefixCost q.1 q.2))) blockComputes)
    (fun xs => by simp [rows, rowBytes, entries, List.flatMap_assoc])

def referencesComputes : Computes encoding Environment.encoding references :=
  ListAccess.rangeComputes encoding encodingNatBool List.length countComputes
    (fun q => suffixCost q.1 q.2) (suffixComputes.andThen UnaryBinary.computes)

def computes : Computes encoding resultEncoding result := pairComputes rowsComputes referencesComputes

variable (tm : FinTM2) [∀ k, Fintype (tm.Γ k)] (e : tm.Γ tm.k₀ ≃ Bool ⊕ Bool)

/-- A real byte generator for the explicit initial plan. The separate
InitialExact module identifies both fields with InitialRows.initial. -/
def initialComputes : Computes InitialPlan.inputEncoding resultEncoding
    (fun p => result (InitialPlan.plan tm e p)) :=
  (InitialPlan.computes tm e).andThen computes

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)
local instance : ∀ k, Fintype (w.verifier.tm.Γ k) := w.verifier.finiteAlphabets

def originalComputes : Computes ea resultEncoding (fun a =>
    result (InitialPlan.plan w.verifier.tm w.verifier.inputAlphabet
      (ea.encode a, VerifierRun.witnessLength w a, capacity w (ea.encode a)))) :=
  (pairComputes (encodeComputes ea)
    (pairComputes (RuntimeParameters.witnessComputes w) (RuntimeParameters.capacityComputes w))).andThen
      (initialComputes w.verifier.tm w.verifier.inputAlphabet)

theorem original_primitive_bound (a : α) :
    primitiveCost (originalComputes w).machine ((originalComputes w).outputs a).steps
      (some (initList (originalComputes w).machine.computer (ea.encode a))) ≤
        (primitivePolynomial (originalComputes w)).eval (ea.encode a).length :=
  computes_primitive_cost (originalComputes w) a

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.PlanRows
