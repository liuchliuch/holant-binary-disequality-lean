import Holant.Proofs.CountingMachines.VerifierCircuit.PrimitiveBlocks

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Structural TM2 statement compilation and held dispatch

Ported reference proof. See the task validation reports.

The recursion is on the actual statement syntax. Dispatch enumerates only the
fixed label alphabet; branch arms are circuits on the same original wires.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Statement

open Holant.LocalDrafts.CountingHardness

open Turing BitLayout
open scoped Classical
variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]

def emit : TM2.Stmt tm.Γ tm.Λ tm.σ → Emit (Address tm C) (Address tm C)
  | .push k f q => Emit.seq (PrimitiveBlocks.push tm C k f) (emit q)
  | .pop k f q => Emit.seq (PrimitiveBlocks.readState tm C k f)
      (Emit.seq (PrimitiveBlocks.pop tm C k) (emit q))
  | .peek k f q => Emit.seq (PrimitiveBlocks.readState tm C k f) (emit q)
  | .load f q => Emit.seq (PrimitiveBlocks.load tm C f) (emit q)
  | .branch f q r => PrimitiveBlocks.choose tm C (PrimitiveBlocks.test tm C f) (emit q) (emit r)
  | .goto f => PrimitiveBlocks.goto tm C f
  | .halt => PrimitiveBlocks.halt tm C

def value : TM2.Stmt tm.Γ tm.Λ tm.σ → Bits tm C → Bits tm C
  | .push k f q, x => value q (PrimitiveBlocks.pushValue tm C k f x)
  | .pop k f q, x => value q (replacePop tm C (PrimitiveBlocks.readStateValue tm C k f x) k)
  | .peek k f q, x => value q (PrimitiveBlocks.readStateValue tm C k f x)
  | .load f q, x => value q (PrimitiveBlocks.loadValue tm C f x)
  | .branch f q r, x => fun a => if PrimitiveBlocks.testValue tm C f x then value q x a else value r x a
  | .goto f, x => PrimitiveBlocks.gotoValue tm C f x
  | .halt, x => replaceLabel tm C x (oneHot (none : Option tm.Λ))

theorem denotes (q : TM2.Stmt tm.Γ tm.Λ tm.σ) : Emit.Denotes (emit tm C q) (value tm C q) := by
  induction q with
  | push k f q ih =>
    simpa only [emit, value] using Emit.seq_denotes (PrimitiveBlocks.push_denotes tm C k f) ih
  | pop k f q ih =>
    simpa only [emit, value] using Emit.seq_denotes (PrimitiveBlocks.readState_denotes tm C k f)
      (Emit.seq_denotes (PrimitiveBlocks.pop_denotes tm C k) ih)
  | peek k f q ih =>
    simpa only [emit, value] using Emit.seq_denotes (PrimitiveBlocks.readState_denotes tm C k f) ih
  | load f q ih =>
    simpa only [emit, value] using Emit.seq_denotes (PrimitiveBlocks.load_denotes tm C f) ih
  | branch f q r ihq ihr =>
    simpa only [emit, value] using PrimitiveBlocks.choose_denotes tm C
      (PrimitiveBlocks.test_denotes tm C f) ihq ihr
  | goto f => exact PrimitiveBlocks.goto_denotes tm C f
  | halt => exact PrimitiveBlocks.halt_denotes tm C

theorem value_encode (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (p : PackedStep.Packed tm C) :
    value tm C q (encode tm C p) = encode tm C (PackedStep.aux tm C q p) := by
  induction q generalizing p with
  | push k f q ih => simp only [value, PackedStep.aux, PrimitiveBlocks.push_encode, ih]
  | pop k f q ih => simp only [value, PackedStep.aux, PrimitiveBlocks.readState_encode,
      replacePop_encode, ih]
  | peek k f q ih => simp only [value, PackedStep.aux, PrimitiveBlocks.readState_encode, ih]
  | load f q ih => simp only [value, PackedStep.aux, PrimitiveBlocks.load_encode, ih]
  | branch f q r ihq ihr =>
    funext a
    cases hf : f p.2.1 <;>
      simp [value, PackedStep.aux, PrimitiveBlocks.test_encode, hf, ihq, ihr]
  | goto f => exact PrimitiveBlocks.goto_encode tm C f p
  | halt => exact replaceLabel_encode tm C p none

theorem actual_step (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (c : tm.Cfg)
    (hc : ∀ k, (c.stk k).length + VerifierRun.pushes q ≤ C + 1) :
    value tm C q (encode tm C (PackedStep.packRaw tm C c)) =
      encode tm C (PackedStep.packRaw tm C (TM2.stepAux q c.var c.stk)) := by
  rw [value_encode, PackedStep.aux_correct tm C q c hc]

def dispatch : List tm.Λ → Emit (Address tm C) (Address tm C)
  | [] => Emit.id _
  | l :: ls => PrimitiveBlocks.choose tm C
      (Emit.route (fun _ : Unit => labelAddr tm C (some l)))
      (emit tm C (tm.m l)) (dispatch ls)

def dispatchValue : List tm.Λ → Bits tm C → Bits tm C
  | [], x => x
  | l :: ls, x => fun a => if x (labelAddr tm C (some l)) then value tm C (tm.m l) x a
      else dispatchValue ls x a

theorem dispatch_denotes (ls : List tm.Λ) :
    Emit.Denotes (dispatch tm C ls) (dispatchValue tm C ls) := by
  induction ls with
  | nil => exact Emit.route_denotes _
  | cons l ls ih =>
    simpa only [dispatch, dispatchValue] using PrimitiveBlocks.choose_denotes tm C
      (Emit.route_denotes (fun _ : Unit => labelAddr tm C (some l)))
      (denotes tm C (tm.m l)) ih

theorem dispatch_none (ls : List tm.Λ) (p : PackedStep.Packed tm C) (hp : p.1 = none) :
    dispatchValue tm C ls (encode tm C p) = encode tm C p := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    funext a
    simp [dispatchValue, encode, labelAddr, oneHot, hp, ih]

theorem dispatch_some (ls : List tm.Λ) (l : tm.Λ) (hl : l ∈ ls)
    (p : PackedStep.Packed tm C) (hp : p.1 = some l) :
    dispatchValue tm C ls (encode tm C p) = encode tm C (PackedStep.aux tm C (tm.m l) p) := by
  induction ls with
  | nil => simp at hl
  | cons j ls ih =>
    by_cases hj : l = j
    · subst j
      funext a
      simp [dispatchValue, encode, labelAddr, oneHot, hp, value_encode]
    · have hm : l ∈ ls := by simpa [hj] using hl
      funext a
      simp [dispatchValue, encode, labelAddr, oneHot, hp, hj, ih hm]

def hold : Emit (Address tm C) (Address tm C) := dispatch tm C (fixedEnum tm.Λ)
def holdValue : Bits tm C → Bits tm C := dispatchValue tm C (fixedEnum tm.Λ)

theorem hold_denotes : Emit.Denotes (hold tm C) (holdValue tm C) := dispatch_denotes tm C _

theorem hold_encode (p : PackedStep.Packed tm C) :
    holdValue tm C (encode tm C p) = encode tm C (PackedStep.hold tm C p) := by
  cases hp : p.1 with
  | none => simpa [holdValue, PackedStep.hold, hp] using dispatch_none tm C (fixedEnum tm.Λ) p hp
  | some l => simpa [holdValue, PackedStep.hold, hp] using
      dispatch_some tm C (fixedEnum tm.Λ) l (mem_fixedEnum l) p hp

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Statement
