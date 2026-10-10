import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.Block

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Every source instruction compiles to actual Boolean
push/pop/load/branch/goto/halt syntax. The source finite state is a fixed control
table; a runtime symbol is never decoded by a List operation or step callback. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Compiler
open Turing Computability Holant.Complexity
variable (m : BinaryMachine)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
abbrev State := Block.State m

def statement : m.core.Stmt → TM2.Stmt (fun _ : m.core.K => Bool) m.core.Λ (State m)
  | .push k f q => Block.pushVector m k (Code.width m k)
      (fun i v => Code.bit m k (f v.1) i) (statement q)
  | .pop k f q => Block.readSymbol m k (fun head =>
      .load (fun v => Block.clear m (f v.1 head)) (statement q))
  | .peek k f q => Block.peekSymbol m k (fun head =>
      .load (fun v => Block.clear m (f v.1 head)) (statement q))
  | .load f q => .load (fun v => Block.clear m (f v.1)) (statement q)
  | .branch f q r => .branch (fun v => f v.1) (statement q) (statement r)
  | .goto f => .goto (fun v => f v.1)
  | .halt => .halt

abbrev computer : FinTM2 where
  K := m.core.K
  k₀ := m.core.k₀
  k₁ := m.core.k₁
  Γ := fun _ => Bool
  Λ := m.core.Λ
  main := m.core.main
  σ := State m
  initialState := Block.clear m m.core.initialState
  m l := statement m (m.core.m l)

abbrev machine : BinaryMachine where
  core := computer m
  alternate l := statement m (m.alternate l)
  split := m.split
  alphabets _ := Bool.fintype

def cfg (c : m.Config) : (machine m).Config := ⟨c.l,Block.clear m c.var,Code.tapes m c.stk⟩

theorem cfg_injective : Function.Injective (cfg m) := by
  intro c d h
  have hl := congrArg (fun p : (machine m).Config => p.l) h
  have hv := congrArg (fun p : (machine m).Config => p.var.1) h
  have hs := Code.tapes_injective m (congrArg (fun p : (machine m).Config => p.stk) h)
  cases c
  cases d
  cases hl
  cases hv
  cases hs
  rfl

@[simp] theorem cfg_init (word : List (m.core.Γ m.core.k₀)) :
    cfg m (initList m.core word) = initList (computer m) (Code.word m m.core.k₀ word) := by
  simp only [cfg,initList,computer]
  congr 1
  funext k
  by_cases hk : k = m.core.k₀
  · subst k; simp [cfg,Code.tapes,initList,computer]
  · simp [cfg,Code.tapes,Code.word,initList,computer,hk]

/-- The fundamental operational producer. The mathematical coded-tape view
occurs only in the theorem; the program body is the syntax above. -/
theorem statement_stepAux (q : m.core.Stmt) (v : m.core.σ)
    (S : ∀ k, List (m.core.Γ k)) :
    TM2.stepAux (statement m q) (Block.clear m v) (Code.tapes m S) =
      cfg m (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    rw [statement,Block.pushVector_eval]
    change TM2.stepAux (statement m q) (Block.clear m v)
      (Function.update (Code.tapes m S) k (Code.symbol m k (f v)++Code.tapes m S k)) = _
    rw [Code.tapes_cons,ih]
    rfl
  | pop k f q ih =>
    rw [statement,Block.read_word]
    simpa only [TM2.stepAux,Block.clear] using ih (f v (S k).head?) (Function.update S k (S k).tail)
  | peek k f q ih =>
    rw [statement,Block.peek_word]
    simpa only [TM2.stepAux,Block.clear] using ih (f v (S k).head?) S
  | load f q ih => simpa only [statement,TM2.stepAux,Block.clear] using ih (f v) S
  | branch f q r hq hr =>
    cases hb : f v <;> simp only [statement,TM2.stepAux,Block.clear,hb,Bool.false_eq_true,ite_false,ite_true] <;> first | exact hq v S | exact hr v S
  | goto f => rfl
  | halt => rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Compiler
