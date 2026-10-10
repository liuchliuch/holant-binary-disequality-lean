import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.Blocks

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Row-level compiler for all original TM2 statements

Ported reference proof. See the task validation reports.

Every case is checked against the already constructed `Statement.emit` by
`Rows.Exact`, not merely by equality of Boolean denotations.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.StatementRows


open Turing BitLayout
open scoped Classical
variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]
abbrev Addr := Address tm C

def load (f : tm.σ → tm.σ) : Rows.Run (Addr tm C) (Addr tm C) :=
  Rows.renameOutput (Rows.parallel (Rows.route id)
    (Rows.renameInput (PrimitiveBlocks.stateRoute tm C) (Rows.table f))) (PrimitiveBlocks.stateOutput tm C)

def readState (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) : Rows.Run (Addr tm C) (Addr tm C) :=
  Rows.renameOutput (Rows.parallel (Rows.route id)
    (Rows.renameInput (PrimitiveBlocks.headRoute tm C k) (Rows.table₂ f))) (PrimitiveBlocks.stateOutput tm C)

def push (k : tm.K) (f : tm.σ → tm.Γ k) : Rows.Run (Addr tm C) (Addr tm C) :=
  Rows.renameOutput (Rows.parallel (Rows.route id)
    (Rows.renameInput (PrimitiveBlocks.stateRoute tm C) (Rows.table (fun s => some (f s)))))
      (PrimitiveBlocks.pushOutput tm C k)

def pop (k : tm.K) : Rows.Run (Addr tm C) (Addr tm C) :=
  Rows.renameOutput (Rows.parallel (Rows.route id)
    (Rows.tabulate (fixedEnum (Option (tm.Γ k))) mem_fixedEnum
      (fun a => Rows.constant (oneHot (none : Option (tm.Γ k)) a)))) (PrimitiveBlocks.popOutput tm C k)

def goto (f : tm.σ → tm.Λ) : Rows.Run (Addr tm C) (Addr tm C) :=
  Rows.renameOutput (Rows.parallel (Rows.route id)
    (Rows.renameInput (PrimitiveBlocks.stateRoute tm C) (Rows.table (fun s => some (f s)))))
      (PrimitiveBlocks.labelOutput tm C)

def halt : Rows.Run (Addr tm C) (Addr tm C) :=
  Rows.renameOutput (Rows.parallel (Rows.route id)
    (Rows.tabulate (fixedEnum (Option tm.Λ)) mem_fixedEnum
      (fun l => Rows.constant (oneHot (none : Option tm.Λ) l)))) (PrimitiveBlocks.labelOutput tm C)

def test (f : tm.σ → Bool) : Rows.Run (Addr tm C) Unit :=
  Rows.renameOutput (Rows.renameInput (PrimitiveBlocks.stateRoute tm C) (Rows.table f)) (fun _ => true)

def choose (t : Rows.Run (Addr tm C) Unit) (p q : Rows.Run (Addr tm C) (Addr tm C)) :
    Rows.Run (Addr tm C) (Addr tm C) :=
  Rows.seq (Rows.parallel t (Rows.parallel p q))
    (Rows.tabulate (addresses tm C) (mem_addresses tm C)
      (fun a => Rows.mux (.inl ()) (.inr (.inl a)) (.inr (.inr a))))

theorem load_exact (f : tm.σ → tm.σ) : Rows.Exact (PrimitiveBlocks.load tm C f) (load tm C f) :=
  Rows.renameOutput_exact (Rows.parallel_exact (Rows.route_exact _)
    (Rows.renameInput_exact _ (Rows.table_exact f))) _

theorem readState_exact (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    Rows.Exact (PrimitiveBlocks.readState tm C k f) (readState tm C k f) :=
  Rows.renameOutput_exact (Rows.parallel_exact (Rows.route_exact _)
    (Rows.renameInput_exact _ (Rows.table₂_exact f))) _

theorem push_exact (k : tm.K) (f : tm.σ → tm.Γ k) :
    Rows.Exact (PrimitiveBlocks.push tm C k f) (push tm C k f) :=
  Rows.renameOutput_exact (Rows.parallel_exact (Rows.route_exact _)
    (Rows.renameInput_exact _ (Rows.table_exact _))) _

theorem pop_exact (k : tm.K) : Rows.Exact (PrimitiveBlocks.pop tm C k) (pop tm C k) :=
  Rows.renameOutput_exact (Rows.parallel_exact (Rows.route_exact _)
    (Rows.tabulate_exact _ _ _ _ (fun _ => Rows.constant_exact _))) _

theorem goto_exact (f : tm.σ → tm.Λ) : Rows.Exact (PrimitiveBlocks.goto tm C f) (goto tm C f) :=
  Rows.renameOutput_exact (Rows.parallel_exact (Rows.route_exact _)
    (Rows.renameInput_exact _ (Rows.table_exact _))) _

theorem halt_exact : Rows.Exact (PrimitiveBlocks.halt tm C) (halt tm C) :=
  Rows.renameOutput_exact (Rows.parallel_exact (Rows.route_exact _)
    (Rows.tabulate_exact _ _ _ _ (fun _ => Rows.constant_exact _))) _

theorem test_exact (f : tm.σ → Bool) : Rows.Exact (PrimitiveBlocks.test tm C f) (test tm C f) :=
  Rows.renameOutput_exact (Rows.renameInput_exact _ (Rows.table_exact _)) _

theorem choose_exact {t : Emit (Addr tm C) Unit} {p q : Emit (Addr tm C) (Addr tm C)}
    {rt : Rows.Run (Addr tm C) Unit} {rp rq : Rows.Run (Addr tm C) (Addr tm C)}
    (ht : Rows.Exact t rt) (hp : Rows.Exact p rp) (hq : Rows.Exact q rq) :
    Rows.Exact (PrimitiveBlocks.choose tm C t p q) (choose tm C rt rp rq) :=
  Rows.seq_exact (Rows.parallel_exact ht (Rows.parallel_exact hp hq))
    (Rows.tabulate_exact _ _ _ _ (fun _ => Rows.mux_exact _ _ _))

def statement : TM2.Stmt tm.Γ tm.Λ tm.σ → Rows.Run (Addr tm C) (Addr tm C)
  | .push k f q => Rows.seq (push tm C k f) (statement q)
  | .pop k f q => Rows.seq (readState tm C k f) (Rows.seq (pop tm C k) (statement q))
  | .peek k f q => Rows.seq (readState tm C k f) (statement q)
  | .load f q => Rows.seq (load tm C f) (statement q)
  | .branch f q r => choose tm C (test tm C f) (statement q) (statement r)
  | .goto f => goto tm C f
  | .halt => halt tm C

theorem statement_exact (q : TM2.Stmt tm.Γ tm.Λ tm.σ) :
    Rows.Exact (Statement.emit tm C q) (statement tm C q) := by
  induction q with
  | push k f q ih => exact Rows.seq_exact (push_exact tm C k f) ih
  | pop k f q ih => exact Rows.seq_exact (readState_exact tm C k f) (Rows.seq_exact (pop_exact tm C k) ih)
  | peek k f q ih => exact Rows.seq_exact (readState_exact tm C k f) ih
  | load f q ih => exact Rows.seq_exact (load_exact tm C f) ih
  | branch f q r ihq ihr => exact choose_exact tm C (test_exact tm C f) ihq ihr
  | goto f => exact goto_exact tm C f
  | halt => exact halt_exact tm C

def dispatch : List tm.Λ → Rows.Run (Addr tm C) (Addr tm C)
  | [] => Rows.route id
  | l :: ls => choose tm C (Rows.route (fun _ : Unit => labelAddr tm C (some l)))
      (statement tm C (tm.m l)) (dispatch ls)

theorem dispatch_exact (ls : List tm.Λ) : Rows.Exact (Statement.dispatch tm C ls) (dispatch tm C ls) := by
  induction ls with
  | nil => exact Rows.route_exact _
  | cons l ls ih => exact choose_exact tm C (Rows.route_exact _) (statement_exact tm C _) ih

def hold : Rows.Run (Addr tm C) (Addr tm C) := dispatch tm C (fixedEnum tm.Λ)
theorem hold_exact : Rows.Exact (Statement.hold tm C) (hold tm C) := dispatch_exact tm C _

def unroll : ℕ → Rows.Run (Addr tm C) (Addr tm C)
  | 0 => Rows.route id
  | T + 1 => Rows.seq (unroll T) (hold tm C)

theorem unroll_exact (T : ℕ) : Rows.Exact (Unroll.emit tm C T) (unroll tm C T) := by
  induction T with
  | zero => exact Rows.route_exact _
  | succ T ih => exact Rows.seq_exact ih (hold_exact tm C)

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.StatementRows
