import Holant.Proofs.CountingMachines.VerifierCircuit.Compile
import Mathlib.Tactic.Linarith

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Exact emitted gate counts and their capacity dependence

Ported reference proof. See the task validation reports.

These are structural counts of existing `Circuit` nodes. They do not stand in
for a physical byte-output program or a primitive-step complexity theorem.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit


open Turing BitLayout
open scoped Classical

namespace Emit

theorem renameInput_adds {I J O : Type} (r : I → J) {p : Emit I O} {g : ℕ}
    (hp : Adds p g) : Adds (renameInput r p) g := by
  intro A n ctx input k t hk
  exact hp A n ctx (fun i => input (r i)) k t hk

theorem renameOutput_adds {I O P : Type} {p : Emit I O} {g : ℕ}
    (hp : Adds p g) (r : P → O) : Adds (renameOutput p r) g := by
  simpa only [renameOutput, Nat.add_zero] using seq_adds hp (route_adds r)

def tableCost {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) : ℕ :=
  ((fixedEnum B).map (fun b => 3 * ((fixedEnum A).filter (fun a => decide (f a = b))).length + 1)).sum

theorem table_adds {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) :
    Adds (table f) (tableCost f) := tabulate_adds _ _ _ _ (fun _ => listOr_adds _)

def table₂Cost {A B D : Type} [Fintype A] [Fintype B] [Fintype D] [DecidableEq D]
    (f : A → B → D) : ℕ :=
  2 * Fintype.card (A × B) + tableCost (fun ab : A × B => f ab.1 ab.2)

theorem table₂_adds {A B D : Type} [Fintype A] [Fintype B] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq D] (f : A → B → D) :
    Adds (table₂ f) (table₂Cost f) := by
  have hc : Adds (cross (A := A) (B := B)) (2 * Fintype.card (A × B)) := by
    simpa [cross, Nat.mul_comm] using tabulate_adds (fixedEnum (A × B)) mem_fixedEnum
      (fun ab : A × B => and (I := A ⊕ B) (.inl ab.1) (.inr ab.2)) (fun _ => 2) (fun _ => and_adds _ _)
  exact seq_adds hc (table_adds _)

end Emit

namespace GateCost

variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]

def width : ℕ := (addresses tm C).length

theorem width_le : width tm C ≤ width tm 0 * (C + 1) := by
  simp only [width, addresses_length]
  nlinarith

theorem load_adds (f : tm.σ → tm.σ) :
    Emit.Adds (PrimitiveBlocks.load tm C f) (Emit.tableCost f) := by
  simpa [PrimitiveBlocks.load, Emit.id] using Emit.renameOutput_adds
    (Emit.parallel_adds (Emit.route_adds (fun a : Address tm C => a))
      (Emit.renameInput_adds _ (Emit.table_adds f))) (PrimitiveBlocks.stateOutput tm C)

theorem readState_adds (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    Emit.Adds (PrimitiveBlocks.readState tm C k f) (Emit.table₂Cost f) := by
  simpa [PrimitiveBlocks.readState, Emit.id] using Emit.renameOutput_adds
    (Emit.parallel_adds (Emit.route_adds (fun a : Address tm C => a))
      (Emit.renameInput_adds _ (Emit.table₂_adds f))) (PrimitiveBlocks.stateOutput tm C)

theorem push_adds (k : tm.K) (f : tm.σ → tm.Γ k) :
    Emit.Adds (PrimitiveBlocks.push tm C k f) (Emit.tableCost (fun s => some (f s))) := by
  simpa [PrimitiveBlocks.push, Emit.id] using Emit.renameOutput_adds
    (Emit.parallel_adds (Emit.route_adds (fun a : Address tm C => a))
      (Emit.renameInput_adds _ (Emit.table_adds (fun s => some (f s))))) (PrimitiveBlocks.pushOutput tm C k)

theorem pop_adds (k : tm.K) :
    Emit.Adds (PrimitiveBlocks.pop tm C k) (Fintype.card (Option (tm.Γ k))) := by
  have he : Emit.Adds (PrimitiveBlocks.emptyCell tm C k) (Fintype.card (Option (tm.Γ k))) := by
    simpa [PrimitiveBlocks.emptyCell] using Emit.tabulate_adds (fixedEnum (Option (tm.Γ k))) mem_fixedEnum
      (fun a => Emit.constant (I := Address tm C) (oneHot (none : Option (tm.Γ k)) a))
      (fun _ => 1) (fun _ => Emit.constant_adds _)
  simpa [PrimitiveBlocks.pop, Emit.id] using Emit.renameOutput_adds
    (Emit.parallel_adds (Emit.route_adds (fun a : Address tm C => a)) he) (PrimitiveBlocks.popOutput tm C k)

theorem goto_adds (f : tm.σ → tm.Λ) :
    Emit.Adds (PrimitiveBlocks.goto tm C f) (Emit.tableCost (fun s => some (f s))) := by
  simpa [PrimitiveBlocks.goto, Emit.id] using Emit.renameOutput_adds
    (Emit.parallel_adds (Emit.route_adds (fun a : Address tm C => a))
      (Emit.renameInput_adds _ (Emit.table_adds (fun s => some (f s))))) (PrimitiveBlocks.labelOutput tm C)

theorem halt_adds : Emit.Adds (PrimitiveBlocks.halt tm C) (Fintype.card (Option tm.Λ)) := by
  have he : Emit.Adds (Emit.tabulate (fixedEnum (Option tm.Λ)) mem_fixedEnum
      (fun l => Emit.constant (I := Address tm C) (oneHot (none : Option tm.Λ) l)))
      (Fintype.card (Option tm.Λ)) := by
    simpa using Emit.tabulate_adds (fixedEnum (Option tm.Λ)) mem_fixedEnum
      (fun l => Emit.constant (I := Address tm C) (oneHot (none : Option tm.Λ) l))
      (fun _ => 1) (fun _ => Emit.constant_adds _)
  simpa [PrimitiveBlocks.halt, Emit.id] using Emit.renameOutput_adds
    (Emit.parallel_adds (Emit.route_adds (fun a : Address tm C => a)) he) (PrimitiveBlocks.labelOutput tm C)

theorem test_adds (f : tm.σ → Bool) : Emit.Adds (PrimitiveBlocks.test tm C f) (Emit.tableCost f) :=
  Emit.renameOutput_adds (Emit.renameInput_adds _ (Emit.table_adds f)) _

theorem choose_adds {t : Emit (Address tm C) Unit} {p q : Emit (Address tm C) (Address tm C)}
    {a b c : ℕ} (ht : Emit.Adds t a) (hp : Emit.Adds p b) (hq : Emit.Adds q c) :
    Emit.Adds (PrimitiveBlocks.choose tm C t p q) (a + (b + c) + 4 * width tm C) := by
  have hm : Emit.Adds (Emit.tabulate (addresses tm C) (mem_addresses tm C)
      (fun a => Emit.mux (I := Unit ⊕ (Address tm C ⊕ Address tm C)) (.inl ()) (.inr (.inl a)) (.inr (.inr a)))) (4 * width tm C) := by
    simpa [width, Nat.mul_comm] using Emit.tabulate_adds (addresses tm C) (mem_addresses tm C)
      (fun a => Emit.mux (I := Unit ⊕ (Address tm C ⊕ Address tm C)) (.inl ()) (.inr (.inl a)) (.inr (.inr a))) (fun _ => 4)
      (fun _ => Emit.mux_adds _ _ _)
  exact Emit.seq_adds (Emit.parallel_adds ht (Emit.parallel_adds hp hq)) hm

def statement : TM2.Stmt tm.Γ tm.Λ tm.σ → ℕ
  | .push _ f q => Emit.tableCost (fun s => some (f s)) + statement q
  | .pop k f q => Emit.table₂Cost f + (Fintype.card (Option (tm.Γ k)) + statement q)
  | .peek _ f q => Emit.table₂Cost f + statement q
  | .load f q => Emit.tableCost f + statement q
  | .branch f q r => Emit.tableCost f + (statement q + statement r) + 4 * width tm C
  | .goto f => Emit.tableCost (fun s => some (f s))
  | .halt => Fintype.card (Option tm.Λ)

theorem statement_adds (q : TM2.Stmt tm.Γ tm.Λ tm.σ) :
    Emit.Adds (Statement.emit tm C q) (statement tm C q) := by
  induction q with
  | push k f q ih => exact Emit.seq_adds (push_adds tm C k f) ih
  | pop k f q ih => exact Emit.seq_adds (readState_adds tm C k f) (Emit.seq_adds (pop_adds tm C k) ih)
  | peek k f q ih => exact Emit.seq_adds (readState_adds tm C k f) ih
  | load f q ih => exact Emit.seq_adds (load_adds tm C f) ih
  | branch f q r ihq ihr => exact choose_adds tm C (test_adds tm C f) ihq ihr
  | goto f => exact goto_adds tm C f
  | halt => exact halt_adds tm C

theorem statement_le (q : TM2.Stmt tm.Γ tm.Λ tm.σ) :
    statement tm C q ≤ statement tm 0 q * (C + 1) := by
  have hw := width_le tm C
  induction q with
  | push k f q ih => simp only [statement]; nlinarith
  | pop k f q ih => simp only [statement]; nlinarith
  | peek k f q ih => simp only [statement]; nlinarith
  | load f q ih => simp only [statement]; nlinarith
  | branch f q r ihq ihr => simp only [statement]; nlinarith
  | goto f => simp only [statement]; nlinarith
  | halt => simp only [statement]; nlinarith

def dispatch : List tm.Λ → ℕ
  | [] => 0
  | l :: ls => statement tm C (tm.m l) + dispatch ls + 4 * width tm C

theorem dispatch_adds (ls : List tm.Λ) : Emit.Adds (Statement.dispatch tm C ls) (dispatch tm C ls) := by
  induction ls with
  | nil => exact Emit.route_adds _
  | cons l ls ih =>
    simpa [dispatch, Statement.dispatch] using
      choose_adds tm C (Emit.route_adds _) (statement_adds tm C (tm.m l)) ih

theorem dispatch_le (ls : List tm.Λ) : dispatch tm C ls ≤ dispatch tm 0 ls * (C + 1) := by
  have hw := width_le tm C
  induction ls with
  | nil => simp [dispatch]
  | cons l ls ih =>
    have hs := statement_le tm C (tm.m l)
    simp only [dispatch]
    nlinarith

def hold : ℕ := dispatch tm C (fixedEnum tm.Λ)

theorem hold_adds : Emit.Adds (Statement.hold tm C) (hold tm C) := dispatch_adds tm C _
theorem hold_le : hold tm C ≤ hold tm 0 * (C + 1) := dispatch_le tm C _

theorem unroll_adds (T : ℕ) : Emit.Adds (Unroll.emit tm C T) (T * hold tm C) := by
  induction T with
  | zero => simpa [Unroll.emit, Emit.id] using (Emit.route_adds (fun a : Address tm C => a))
  | succ T ih => simpa [Unroll.emit, Nat.succ_mul] using Emit.seq_adds ih (hold_adds tm C)

end GateCost
end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit
