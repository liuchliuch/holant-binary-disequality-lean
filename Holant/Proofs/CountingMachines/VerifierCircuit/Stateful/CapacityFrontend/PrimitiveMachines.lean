import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.InitialExact

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
Ported reference proof. See the task validation reports.

Fixed control tables connected to runtime-capacity live arrays. Table inputs
are physically selected; retained references are physically shifted by the
table's emitted gate count before the appropriate real array router runs.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.PrimitiveMachines


open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler BitLayout OutputMachine
open scoped Classical

abbrev Input := ℕ × List ℕ
def inputEncoding := pairEncoding Unary.encoding Environment.encoding
abbrev Output := List Bool × List ℕ
abbrev outputEncoding := PlanRows.resultEncoding
def capComputes : Computes inputEncoding Unary.encoding Prod.fst := Wiring.firstComputes _ _
def envComputes : Computes inputEncoding Environment.encoding Prod.snd := Wiring.secondComputes _ _

/-- Equality-decision instances do not change a finite table's emitted rows. -/
def tableRowsComputes {I O : Type} [Fintype I] [Fintype O] [DecidableEq O] (f : I → O) :
    Computes (FiniteMachine.referenceEncoding I) (FiniteMachine.resultEncoding O)
      (fun env => FiniteMachine.result (Rows.table f env)) := by
  refine congrComputes (FiniteMachine.tableComputes f) ?_
  intro env
  congr 2 <;> exact Subsingleton.elim _ _

def table₂RowsComputes {I O P : Type} [Fintype I] [Fintype O] [Fintype P]
    [DecidableEq I] [DecidableEq O] [DecidableEq P] (f : I → O → P) :
    Computes (FiniteMachine.referenceEncoding (I ⊕ O)) (FiniteMachine.resultEncoding P)
      (fun env => FiniteMachine.result (Rows.table₂ f env)) := by
  refine congrComputes (FiniteMachine.table₂Computes f) ?_
  intro env
  congr 2 <;> exact Subsingleton.elim _ _

variable (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]

def stateRefs (p : Input) (s : tm.σ) := p.2.getD (Layout.stateIndex tm s) 0
def headRefs (k : tm.K) (p : Input) : tm.σ ⊕ Option (tm.Γ k) → ℕ :=
  Sum.elim (stateRefs tm p) (fun a => p.2.getD (Layout.cellIndex tm p.1 k 0 a) 0)

def stateRefsComputes : Computes inputEncoding (FiniteMachine.referenceEncoding tm.σ) (stateRefs tm) :=
  recode (fixedListComputes inputEncoding encodingNatBool (stateRefs tm)
    (fun s => envComputes.andThen
      (FixedGadgetSubstitution.Compiler.getDComputes encodingNatBool (Layout.stateIndex tm s) 0))
    (fixedEnum tm.σ)) id (fun _ => rfl) (fun _ => rfl)

def headRefsComputes (k : tm.K) :
    Computes inputEncoding (FiniteMachine.referenceEncoding (tm.σ ⊕ Option (tm.Γ k))) (headRefs tm k) := by
  let slot : Computes inputEncoding (pairEncoding Unary.encoding Unary.encoding) (fun p => (p.1, 0)) :=
    pairComputes capComputes (constantComputes inputEncoding Unary.encoding 0)
  let provider (a : tm.σ ⊕ Option (tm.Γ k)) : Computes inputEncoding encodingNatBool
      (fun p => headRefs tm k p a) := by
    cases a with
    | inl s =>
      exact envComputes.andThen
        (FixedGadgetSubstitution.Compiler.getDComputes encodingNatBool (Layout.stateIndex tm s) 0)
    | inr a =>
      exact (pairComputes envComputes (slot.andThen (Layout.cellIndexComputes tm k a))).andThen
        (ListAccess.getDComputes encodingNatBool 0)
  exact recode (fixedListComputes inputEncoding encodingNatBool (headRefs tm k) provider
    (fixedEnum (tm.σ ⊕ Option (tm.Γ k)))) id (fun _ => rfl) (fun _ => rfl)

theorem stateRefs_pack (C : ℕ) (env : Address tm C → ℕ) :
    stateRefs tm (C, (addresses tm C).map env) = fun s => env (stateAddr tm C s) := by
  funext s
  exact Layout.read_state tm C env s 0

theorem headRefs_pack (C : ℕ) (env : Address tm C → ℕ) (k : tm.K) :
    headRefs tm k (C, (addresses tm C).map env) =
      fun a => env (PrimitiveBlocks.headRoute tm C k a) := by
  funext a
  cases a with
  | inl s => exact Layout.read_state tm C env s 0
  | inr a => exact Layout.read_cell tm C env k 0 a 0

variable {O : Type} [Fintype O]

def attach (g : ℕ) (router : Routing.Input → List ℕ)
    (block : Input → List Bool × (O → ℕ)) (p : Input) : Output :=
  ((block p).1, router (p.1, Environment.shift g p.2, (fixedEnum O).map (block p).2))

def attachComputes (g : ℕ) (router : Routing.Input → List ℕ)
    (wr : Computes Routing.inputEncoding Environment.encoding router)
    (block : Input → List Bool × (O → ℕ))
    (wb : Computes inputEncoding (FiniteMachine.resultEncoding O) block) :
    Computes inputEncoding outputEncoding (attach g router block) := by
  let rows := wb.andThen (Wiring.firstComputes Frame.wordEncoding (FiniteMachine.referenceEncoding O))
  let refs : Computes inputEncoding Environment.encoding (fun p => (fixedEnum O).map (block p).2) :=
    recode (wb.andThen (Wiring.secondComputes Frame.wordEncoding (FiniteMachine.referenceEncoding O)))
      id (fun _ => rfl) (fun _ => rfl)
  let shifted := (pairComputes (constantComputes inputEncoding encodingNatBool g) envComputes).andThen
    Environment.shiftComputes
  exact pairComputes rows ((pairComputes capComputes (pairComputes shifted refs)).andThen wr)

def load (f : tm.σ → tm.σ) : Input → Output := attach (Emit.tableCost f) (Routing.state tm)
  (fun p => FiniteMachine.result (Rows.table f (stateRefs tm p)))
def loadComputes (f : tm.σ → tm.σ) : Computes inputEncoding outputEncoding (load tm f) :=
  attachComputes _ _ (Routing.stateComputes tm) _
    ((stateRefsComputes tm).andThen (tableRowsComputes f))

def readState (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) : Input → Output :=
  attach (Emit.table₂Cost f) (Routing.state tm)
    (fun p => FiniteMachine.result (Rows.table₂ f (headRefs tm k p)))
def readStateComputes (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    Computes inputEncoding outputEncoding (readState tm k f) :=
  attachComputes _ _ (Routing.stateComputes tm) _
    ((headRefsComputes tm k).andThen (table₂RowsComputes f))

def push (k : tm.K) (f : tm.σ → tm.Γ k) : Input → Output :=
  attach (Emit.tableCost (fun s => some (f s))) (Routing.push tm k)
    (fun p => FiniteMachine.result (Rows.table (fun s => some (f s)) (stateRefs tm p)))
def pushComputes (k : tm.K) (f : tm.σ → tm.Γ k) :
    Computes inputEncoding outputEncoding (push tm k f) :=
  attachComputes _ _ (Routing.pushComputes tm k) _
    ((stateRefsComputes tm).andThen (tableRowsComputes (fun s => some (f s))))

def goto (f : tm.σ → tm.Λ) : Input → Output :=
  attach (Emit.tableCost (fun s => some (f s))) (Routing.label tm)
    (fun p => FiniteMachine.result (Rows.table (fun s => some (f s)) (stateRefs tm p)))
def gotoComputes (f : tm.σ → tm.Λ) : Computes inputEncoding outputEncoding (goto tm f) :=
  attachComputes _ _ (Routing.labelComputes tm) _
    ((stateRefsComputes tm).andThen (tableRowsComputes (fun s => some (f s))))

def emptyBlock (O : Type) [Fintype O] [DecidableEq O] (bits : O → Bool) : List Bool × (O → ℕ) :=
  FiniteMachine.result (Rows.tabulate (fixedEnum O) mem_fixedEnum
    (fun a => Rows.constant (I := Unit) (bits a)) (fun _ => 0))

def pop (k : tm.K) : Input → Output :=
  attach (Fintype.card (Option (tm.Γ k))) (Routing.pop tm k)
    (fun _ => emptyBlock (Option (tm.Γ k)) (oneHot none))
def popComputes (k : tm.K) : Computes inputEncoding outputEncoding (pop tm k) :=
  attachComputes _ _ (Routing.popComputes tm k) _ (constantComputes inputEncoding
    (FiniteMachine.resultEncoding (Option (tm.Γ k))) (emptyBlock _ (oneHot none)))

def halt : Input → Output := attach (Fintype.card (Option tm.Λ)) (Routing.label tm)
  (fun _ => emptyBlock (Option tm.Λ) (oneHot none))
def haltComputes : Computes inputEncoding outputEncoding (halt tm) :=
  attachComputes _ _ (Routing.labelComputes tm) _ (constantComputes inputEncoding
    (FiniteMachine.resultEncoding (Option tm.Λ)) (emptyBlock _ (oneHot none)))

def test (f : tm.σ → Bool) (p : Input) : Output :=
  let r := Rows.table f (stateRefs tm p)
  (rowBytes r.1, [r.2 true])
def testComputes (f : tm.σ → Bool) : Computes inputEncoding outputEncoding (test tm f) := by
  let run := (stateRefsComputes tm).andThen (tableRowsComputes f)
  let rows := run.andThen (Wiring.firstComputes Frame.wordEncoding (FiniteMachine.referenceEncoding Bool))
  let ref := (run.andThen (Wiring.secondComputes Frame.wordEncoding (FiniteMachine.referenceEncoding Bool))).andThen
    (FiniteMachine.getComputes true)
  exact pairComputes rows (congrComputes
    (fixedListComputes inputEncoding encodingNatBool (fun p (_ : Unit) => (Rows.table f (stateRefs tm p)).2 true)
      (fun _ => ref) [()]) (fun _ => rfl))

theorem table_length {I O : Type} [Fintype I] [Fintype O] [DecidableEq O] (f : I → O) (env : I → ℕ) :
    (Rows.table f env).1.length = Emit.tableCost f := by
  simpa [Rows.table, Rows.tabulate, Rows.renameOutput, Rows.seq, Rows.route, Emit.tableCost] using
    Rows.gather_length (fun o => Rows.listOr ((fixedEnum I).filter (fun i => decide (f i = o))))
      (fun o => 3 * ((fixedEnum I).filter (fun i => decide (f i = o))).length + 1)
      (fun _ _ => FiniteMachine.listOr_length _ _) (fixedEnum O) env

def packedResult (C : ℕ) (r : Rows.Result (Address tm C)) : Output :=
  (rowBytes r.1, (addresses tm C).map r.2)

theorem load_eq (C : ℕ) (env : Address tm C → ℕ) (f : tm.σ → tm.σ) :
    load tm f (C, (addresses tm C).map env) = packedResult tm C (StatementRows.load tm C f env) := by
  rw [load, attach, stateRefs_pack]
  have hs := Environment.shift_pack (Emit.tableCost f) (addresses tm C) env
  change Environment.shift _ ((addresses tm C).map env) =
    (addresses tm C).map (Rows.shift _ env) at hs
  rw [hs]
  have hr := Routing.state_eq tm C (Rows.shift (Emit.tableCost f) env)
    (Rows.table f (fun s => env (stateAddr tm C s))).2
  apply Prod.ext
  · simp [packedResult, FiniteMachine.result, StatementRows.load, Rows.renameOutput,
      Rows.seq, Rows.parallel, Rows.route, Rows.renameInput, PrimitiveBlocks.stateRoute]
  · simpa [Routing.input, packedResult, FiniteMachine.result, StatementRows.load,
      Rows.renameOutput, Rows.seq, Rows.parallel, Rows.route, Rows.renameInput,
      table_length, PrimitiveBlocks.stateRoute, Rows.shift] using hr

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.CapacityFrontend.PrimitiveMachines
