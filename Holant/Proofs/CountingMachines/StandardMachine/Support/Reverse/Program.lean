import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Packet
import Holant.Proofs.CountingMachines.StandardMachine.Support.SumStacks

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. A real interpreter round for an arbitrary BinaryMachine.
Two pop transitions read a packet. The third transition checks its canonical
form and executes the same original heterogeneous statement syntax. Original
stack functions are never evaluated by a load/configuration opcode.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Program
open Turing Holant.Complexity
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
variable (m : BinaryMachine)

local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin

abbrev Stack := Unit ⊕ m.core.K
abbrev Alphabet : Stack m → Type := SumStacks.Alphabet m.core.Γ
local instance (k : Stack m) : Fintype (Alphabet m k) := by
  cases k with
  | inl _ => exact inferInstanceAs (Fintype Bool)
  | inr k => exact m.alphabets k
abbrev Label := Unit ⊕ (Option m.core.Λ × Fin 3)
abbrev State := Option Bool × (Option Bool × m.core.σ)

def packet : Stack m := .inl ()
def label (source : Option m.core.Λ) (phase : Fin 3) : Label m := .inr (source,phase)
def reject : Label m := .inl ()
def clear (v : m.core.σ) : State m := (none,none,v)

/-- Literal finite syntax translation. A source goto/halt returns to the packet
reader with the corresponding original label/none, preserving original state.
This is a held source halt, not a fresh nondeterministic branch.
-/
def compileStmt : TM2.Stmt m.core.Γ m.core.Λ m.core.σ →
    TM2.Stmt (Alphabet m) (Label m) (State m)
  | .push k f q => .push (.inr k) (fun v => f v.2.2) (compileStmt q)
  | .pop k f q => .pop (.inr k) (fun v b => clear m (f v.2.2 b)) (compileStmt q)
  | .peek k f q => .peek (.inr k) (fun v b => clear m (f v.2.2 b)) (compileStmt q)
  | .load f q => .load (fun v => clear m (f v.2.2)) (compileStmt q)
  | .branch f q r => .branch (fun v => f v.2.2) (compileStmt q) (compileStmt r)
  | .goto f => .load (fun v => clear m v.2.2)
      (.goto (fun v => label m (some (f v.2.2)) 0))
  | .halt => .load (fun v => clear m v.2.2) (.goto (fun _ => label m none 0))

def ordinaryPacket (v : State m) : Bool := v.1 == some false && v.2.1 == some false
def splitPacket (v : State m) : Bool := v.1 == some true && v.2.1.isSome

def program : Label m → TM2.Stmt (Alphabet m) (Label m) (State m)
  | .inl _ => .halt
  | .inr (source,phase) =>
    if phase = 0 then
      .pop (packet m) (fun v b => (b,v.2)) (.goto (fun _ => label m source 1))
    else if phase = 1 then
      .pop (packet m) (fun v b => (v.1,b,v.2.2)) (.goto (fun _ => label m source 2))
    else match source with
      | none => .branch (ordinaryPacket m)
          (.load (fun v => clear m v.2.2) (.goto (fun _ => label m none 0)))
          (.goto (fun _ => reject m))
      | some l => if m.split l then
          .branch (splitPacket m)
            (.branch (fun v => v.2.1.getD false)
              (compileStmt m (m.alternate l)) (compileStmt m (m.core.m l)))
            (.goto (fun _ => reject m))
        else .branch (ordinaryPacket m) (compileStmt m (m.core.m l))
          (.goto (fun _ => reject m))

/-- The extra input/output stack contains raw packet bits. This component is a
round interpreter; the whole typed-input verifier's staging/cleanup is separate.
-/
def computer : FinTM2 where
  K := Stack m
  k₀ := packet m
  k₁ := packet m
  Γ := Alphabet m
  Λ := Label m
  main := label m (some m.core.main) 0
  σ := State m
  initialState := clear m m.core.initialState
  m := program m

def phaseCfg (phase : Fin 3) (first second : Option Bool) (word : List Bool)
    (c : m.Config) : (computer m).Cfg :=
  ⟨some (label m c.l phase),(first,second,c.var),
    SumStacks.merge m.core.Γ (fun _ : Unit => word) c.stk⟩

def readyCfg (word : List Bool) (c : m.Config) : (computer m).Cfg :=
  phaseCfg m 0 none none word c

def rejectedCfg (first second : Option Bool) (word : List Bool) (c : m.Config) :
    (computer m).Cfg :=
  ⟨some (reject m),(first,second,c.var),
    SumStacks.merge m.core.Γ (fun _ : Unit => word) c.stk⟩

/-- Install the same finite program as a deterministic BinaryMachine solely to
consume the already proved generic prefix/cost/storage observers. No alternate
statement is selected and no choice bit is charged by this component.
-/
def deterministic : BinaryMachine where
  core := computer m
  alternate := program m
  split _ := false
  alphabets key := by
    cases key with
    | inl k => exact inferInstanceAs (Fintype Bool)
    | inr k => exact m.alphabets k

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Program
