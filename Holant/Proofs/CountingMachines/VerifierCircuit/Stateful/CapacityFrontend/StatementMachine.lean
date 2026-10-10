import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.PrimitiveMachines

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Concrete capacity-uniform statement/dispatch byte programs. Branches save the
original array through ordinary pair wiring, compile both arms with explicit
reference shifts, then emit the existing four-gate mux batch. The specification
here is the displayed raw byte algorithm. Its remaining exact bridge to
StatementRows.hold is not assumed or asserted by this file.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.StatementMachine


open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler BitLayout PrimitiveMachines
open scoped Classical

def rowsComputes : Computes outputEncoding Frame.wordEncoding Prod.fst := Wiring.firstComputes _ _
def refsComputes : Computes outputEncoding Environment.encoding Prod.snd := Wiring.secondComputes _ _

def shiftInput (g : ℕ) (p : Input) : Input := (p.1, Environment.shift g p.2)
def shiftInputComputes (g : Input → ℕ) (wg : Computes inputEncoding Unary.encoding g) :
    Computes inputEncoding inputEncoding (fun p => shiftInput (g p) p) :=
  pairComputes capComputes
    ((pairComputes (wg.andThen UnaryBinary.computes) envComputes).andThen Environment.shiftComputes)

def seq (left right : Input → Output) (p : Input) : Output :=
  let a := left p
  let b := right (p.1, a.2)
  (a.1 ++ b.1, b.2)

def seqComputes (left right : Input → Output)
    (wl : Computes inputEncoding outputEncoding left) (wr : Computes inputEncoding outputEncoding right) :
    Computes inputEncoding outputEncoding (seq left right) := by
  let next := (pairComputes capComputes (wl.andThen refsComputes)).andThen wr
  exact pairComputes (joinComputes (wl.andThen rowsComputes) (next.andThen rowsComputes))
    (next.andThen refsComputes)

variable (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]

def width (p : Input) := controlWidth tm + (p.1 + 1) * cellWidth tm
def widthComputes : Computes inputEncoding Unary.encoding (width tm) :=
  capComputes.andThen (Layout.widthComputes tm)

def chooseTriples (select : ℕ) (yes no : List ℕ) (D : ℕ) : List MuxMachine.Triple :=
  (List.range D).map (fun i => (select, yes.getD i 0, no.getD i 0))

abbrev MuxInput := ℕ × (ℕ × (List ℕ × List ℕ))
def muxInputEncoding := pairEncoding Unary.encoding
  (pairEncoding encodingNatBool (pairEncoding Environment.encoding Environment.encoding))

def triplesComputes : Computes muxInputEncoding (framedListEncoding MuxMachine.tripleEncoding)
    (fun p => chooseTriples p.2.1 p.2.2.1 p.2.2.2 p.1) := by
  let cap := Wiring.firstComputes Unary.encoding
    (pairEncoding encodingNatBool (pairEncoding Environment.encoding Environment.encoding))
  let rest := Wiring.secondComputes Unary.encoding
    (pairEncoding encodingNatBool (pairEncoding Environment.encoding Environment.encoding))
  let select := rest.andThen (Wiring.firstComputes _ _)
  let arrays := rest.andThen (Wiring.secondComputes _ _)
  let yes := arrays.andThen (Wiring.firstComputes _ _)
  let no := arrays.andThen (Wiring.secondComputes _ _)
  let context := Wiring.firstComputes muxInputEncoding Unary.encoding
  let index := Wiring.secondComputes muxInputEncoding Unary.encoding
  let provider := pairComputes (context.andThen select)
    (pairComputes
      ((pairComputes (context.andThen yes) index).andThen (ListAccess.getDComputes encodingNatBool 0))
      ((pairComputes (context.andThen no) index).andThen (ListAccess.getDComputes encodingNatBool 0)))
  exact ListAccess.rangeComputes muxInputEncoding MuxMachine.tripleEncoding Prod.fst cap _ provider

def choose (ct cp cq : ℕ → ℕ) (test yes no : Input → Output) (p : Input) : Output :=
  let t := test p
  let a := yes (shiftInput (ct p.1) p)
  let b := no (shiftInput (ct p.1 + cp p.1) p)
  let triples := chooseTriples (t.2.getD 0 0 + (cp p.1 + cq p.1))
    (Environment.shift (cq p.1) a.2) b.2 (width tm p)
  (t.1 ++ (a.1 ++ (b.1 ++ OutputMachine.rowBytes (MuxMachine.batchRecords triples))),
    CanonicalMachine.values (width tm p))

def chooseComputes (ct cp cq : ℕ → ℕ)
    (wt : Computes Unary.encoding Unary.encoding ct)
    (wp : Computes Unary.encoding Unary.encoding cp)
    (wq : Computes Unary.encoding Unary.encoding cq)
    (test yes no : Input → Output)
    (rt : Computes inputEncoding outputEncoding test)
    (rp : Computes inputEncoding outputEncoding yes)
    (rq : Computes inputEncoding outputEncoding no) :
    Computes inputEncoding outputEncoding (choose tm ct cp cq test yes no) := by
  let gt := capComputes.andThen wt
  let gp := capComputes.andThen wp
  let gq := capComputes.andThen wq
  let left := (shiftInputComputes _ gt).andThen rp
  let right := (shiftInputComputes _ ((pairComputes gt gp).andThen Unary.addComputes)).andThen rq
  let retained := ((rt.andThen refsComputes).andThen
    (FixedGadgetSubstitution.Compiler.getDComputes encodingNatBool 0 0))
  let remaining := ((pairComputes gp gq).andThen Unary.addComputes).andThen UnaryBinary.computes
  let select := (pairComputes retained remaining).andThen addComputes
  let yesRefs := (pairComputes (gq.andThen UnaryBinary.computes) (left.andThen refsComputes)).andThen
    Environment.shiftComputes
  let args := pairComputes (widthComputes tm)
    (pairComputes select (pairComputes yesRefs (right.andThen refsComputes)))
  let mux := (args.andThen triplesComputes).andThen MuxMachine.batchComputes
  exact pairComputes
    (joinComputes (rt.andThen rowsComputes)
      (joinComputes (left.andThen rowsComputes) (joinComputes (right.andThen rowsComputes) mux)))
    ((widthComputes tm).andThen CanonicalMachine.computes)

def constCost (g : ℕ) : Computes Unary.encoding Unary.encoding (fun _ => g) :=
  constantComputes Unary.encoding Unary.encoding g
def plusCost {f g : ℕ → ℕ} (u : Computes Unary.encoding Unary.encoding f)
    (v : Computes Unary.encoding Unary.encoding g) :
    Computes Unary.encoding Unary.encoding (fun C => f C + g C) :=
  (pairComputes u v).andThen Unary.addComputes
def muxCostComputes : Computes Unary.encoding Unary.encoding (fun C => 4 * GateCost.width tm C) :=
  congrComputes ((Layout.widthComputes tm).andThen (Unary.scaleComputes 4))
    (fun C => by rw [GateCost.width, addresses_length]; rfl)

def costComputes : (q : TM2.Stmt tm.Γ tm.Λ tm.σ) →
    Computes Unary.encoding Unary.encoding (fun C => GateCost.statement tm C q)
  | .push _ f q => plusCost (constCost (Emit.tableCost (fun s => some (f s)))) (costComputes q)
  | .pop k f q => plusCost (constCost (Emit.table₂Cost f))
      (plusCost (constCost (Fintype.card (Option (tm.Γ k)))) (costComputes q))
  | .peek _ f q => plusCost (constCost (Emit.table₂Cost f)) (costComputes q)
  | .load f q => plusCost (constCost (Emit.tableCost f)) (costComputes q)
  | .branch f q r => plusCost
      (plusCost (constCost (Emit.tableCost f)) (plusCost (costComputes q) (costComputes r)))
      (muxCostComputes tm)
  | .goto f => constCost (Emit.tableCost (fun s => some (f s)))
  | .halt => constCost (Fintype.card (Option tm.Λ))

def statement : TM2.Stmt tm.Γ tm.Λ tm.σ → Input → Output
  | .push k f q => seq (PrimitiveMachines.push tm k f) (statement q)
  | .pop k f q => seq (PrimitiveMachines.readState tm k f) (seq (PrimitiveMachines.pop tm k) (statement q))
  | .peek k f q => seq (PrimitiveMachines.readState tm k f) (statement q)
  | .load f q => seq (PrimitiveMachines.load tm f) (statement q)
  | .branch f q r => choose tm (fun _ => Emit.tableCost f)
      (fun C => GateCost.statement tm C q) (fun C => GateCost.statement tm C r)
      (PrimitiveMachines.test tm f) (statement q) (statement r)
  | .goto f => PrimitiveMachines.goto tm f
  | .halt => PrimitiveMachines.halt tm

def statementComputes : (q : TM2.Stmt tm.Γ tm.Λ tm.σ) →
    Computes inputEncoding outputEncoding (statement tm q)
  | .push k f q => seqComputes _ _ (PrimitiveMachines.pushComputes tm k f) (statementComputes q)
  | .pop k f q => seqComputes _ _ (PrimitiveMachines.readStateComputes tm k f)
      (seqComputes _ _ (PrimitiveMachines.popComputes tm k) (statementComputes q))
  | .peek k f q => seqComputes _ _ (PrimitiveMachines.readStateComputes tm k f) (statementComputes q)
  | .load f q => seqComputes _ _ (PrimitiveMachines.loadComputes tm f) (statementComputes q)
  | .branch f q r => chooseComputes tm _ _ _ (constCost (Emit.tableCost f))
      (costComputes tm q) (costComputes tm r) _ _ _ (PrimitiveMachines.testComputes tm f)
      (statementComputes q) (statementComputes r)
  | .goto f => PrimitiveMachines.gotoComputes tm f
  | .halt => PrimitiveMachines.haltComputes tm

def identityComputes : Computes inputEncoding outputEncoding (fun p => ([], p.2)) :=
  pairComputes (constantComputes inputEncoding Frame.wordEncoding []) envComputes
def labelTest (l : tm.Λ) (p : Input) : Output := ([], [p.2.getD (Layout.rank (some l)) 0])
def labelTestComputes (l : tm.Λ) : Computes inputEncoding outputEncoding (labelTest tm l) :=
  pairComputes (constantComputes inputEncoding Frame.wordEncoding [])
    (fixedListComputes inputEncoding encodingNatBool
      (fun p (_ : Unit) => p.2.getD (Layout.rank (some l)) 0)
      (fun _ => envComputes.andThen
        (FixedGadgetSubstitution.Compiler.getDComputes encodingNatBool (Layout.rank (some l)) 0)) [()])

def dispatchCostComputes : (ls : List tm.Λ) →
    Computes Unary.encoding Unary.encoding (fun C => GateCost.dispatch tm C ls)
  | [] => constCost 0
  | l :: ls => plusCost (plusCost (costComputes tm (tm.m l)) (dispatchCostComputes ls)) (muxCostComputes tm)
def dispatch : List tm.Λ → Input → Output
  | [] => fun p => ([], p.2)
  | l :: ls => choose tm (fun _ => 0) (fun C => GateCost.statement tm C (tm.m l))
      (fun C => GateCost.dispatch tm C ls) (labelTest tm l) (statement tm (tm.m l)) (dispatch ls)
def dispatchComputes : (ls : List tm.Λ) → Computes inputEncoding outputEncoding (dispatch tm ls)
  | [] => identityComputes
  | l :: ls => chooseComputes tm _ _ _ (constCost 0) (costComputes tm (tm.m l)) (dispatchCostComputes tm ls)
      _ _ _ (labelTestComputes tm l) (statementComputes tm (tm.m l)) (dispatchComputes ls)
def holdComputes : Computes inputEncoding outputEncoding (dispatch tm (fixedEnum tm.Λ)) :=
  dispatchComputes tm (fixedEnum tm.Λ)

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.StatementMachine
