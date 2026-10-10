import Holant.Proofs.CountingMachines.StandardMachine.Support.Source

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. A literal finite continuation at each original halt leaf.
It reads the original output tape and every original work tape, restores the
output head, and stores the result in finite control. It neither receives a
desired flag nor inspects a configuration as a machine instruction. Original
labels, stack alphabets, split sites and macro-transition clocks are unchanged.
The extra elementary instructions are charged by the real statement budget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
open Turing Computability Holant.Complexity
variable (m : BinaryMachine) (trueSymbol : m.core.Γ m.core.k₁)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k
local instance : DecidableEq m.core.σ := Classical.decEq _
local instance : DecidableEq (m.core.Γ m.core.k₁) := Classical.decEq _

abbrev State := m.core.σ × Option (m.core.Γ m.core.k₁) × Bool
def clear (v : m.core.σ) : State m := (v,none,false)
def keys : List m.core.K := List.ofFn (Fintype.equivFin m.core.K).symm

def scanVerdict : List m.core.K → (∀ k, List (m.core.Γ k)) → Bool → Bool
  | [],_,b => b
  | k::rest,S,b => scanVerdict rest S
      (if k = m.core.k₁ then b else b && (S k).isEmpty)

/-- Mathematical specification of the literal EOF tests below. -/
def tapeVerdict (v : m.core.σ) (S : ∀ k, List (m.core.Γ k)) : Bool :=
  scanVerdict m (keys m) S (decide (v = m.core.initialState) &&
    decide (S m.core.k₁ = [trueSymbol]))

def scan : List m.core.K → TM2.Stmt m.core.Γ m.core.Λ (State m)
  | [] => .load (fun v => (v.1,none,v.2.2)) .halt
  | k::rest => if k = m.core.k₁ then scan rest else
      .peek k (fun v head => (v.1,v.2.1,v.2.2 && head.isNone)) (scan rest)

/-- The pop records the actual head. The following peek checks full EOF.
Restoration pushes precisely that recorded symbol, even on a rejecting tape.
Thus output/input aliases and every dirty rejecting tape remain unchanged. -/
def observer : TM2.Stmt m.core.Γ m.core.Λ (State m) :=
  .load (fun v => (v.1,none,decide (v.1 = m.core.initialState)))
    (.pop m.core.k₁ (fun v head =>
      (v.1,head,v.2.2 && decide (head = some trueSymbol)))
      (.peek m.core.k₁ (fun v head => (v.1,v.2.1,v.2.2 && head.isNone))
        (.branch (fun v => v.2.1.isSome)
          (.push m.core.k₁ (fun v => v.2.1.getD trueSymbol) (scan m (keys m)))
          (scan m (keys m)))))

/-- Structural syntax translation. Only the halt leaf receives the finite
observer continuation; no source instruction or branch predicate is replaced
by a host-level step/evaluation function. -/
def statement : TM2.Stmt m.core.Γ m.core.Λ m.core.σ →
    TM2.Stmt m.core.Γ m.core.Λ (State m)
  | .push k f q => .push k (fun v => f v.1) (statement q)
  | .pop k f q => .pop k (fun v head => clear m (f v.1 head)) (statement q)
  | .peek k f q => .peek k (fun v head => clear m (f v.1 head)) (statement q)
  | .load f q => .load (fun v => clear m (f v.1)) (statement q)
  | .branch f q r => .branch (fun v => f v.1) (statement q) (statement r)
  | .goto f => .goto (fun v => f v.1)
  | .halt => observer m trueSymbol

abbrev computer : FinTM2 where
  K := m.core.K
  k₀ := m.core.k₀
  k₁ := m.core.k₁
  Γ := m.core.Γ
  Λ := m.core.Λ
  main := m.core.main
  σ := State m
  initialState := clear m m.core.initialState
  m l := statement m trueSymbol (m.core.m l)

abbrev machine : BinaryMachine where
  core := computer m trueSymbol
  alternate l := statement m trueSymbol (m.alternate l)
  split := m.split
  alphabets := m.alphabets

/-- This control bit is produced by observer, rather than supplied as a
table on the original state space. -/
def acceptControl : State m → Bool := fun v => v.2.2

def liftCfg (c : m.Config) : (machine m trueSymbol).Config :=
  ⟨c.l,(c.var,none,if c.l.isNone then tapeVerdict m trueSymbol c.var c.stk else false),c.stk⟩

def forget (c : (machine m trueSymbol).Config) : m.Config := ⟨c.l,c.var.1,c.stk⟩

@[simp] theorem forget_lift (c : m.Config) : forget m trueSymbol (liftCfg m trueSymbol c) = c := by
  cases c
  rfl

theorem lift_injective : Function.Injective (liftCfg m trueSymbol) := by
  intro c d h
  exact congrArg (forget m trueSymbol) h

@[simp] theorem lift_init (word : List (m.core.Γ m.core.k₀)) :
    liftCfg m trueSymbol (initList m.core word) = initList (computer m trueSymbol) word := by
  rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
