import Holant.Proofs.CountingMachines.StandardMachine.Support.TapeMicrostepBudgetCore

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. One finite nondeterministic TM0 table. Boundary labels
are retained at goto, since the deterministic TM1to0 compiler otherwise stores
the target body and loses the original split label. Each real edge performs
exactly one TM0 move/write. Loads/tests are the same finite transition-table
calculation as trAux; neither a tape decoder nor a whole-row executor is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveDispatcher.Program
open Turing Computability Holant.Complexity
variable (m : BinaryMachine)
abbrev Alphabet := TapeSimulation.Alphabet m
abbrev Label := TapeSimulation.Label m
abbrev Stmt := TM1.Stmt (Alphabet m) (Label m) m.core.σ
abbrev PC := TapeMicrostepBudget.PrimitiveControl m
abbrev Node := Label m ⊕ PC m
abbrev Control := Node m × m.core.σ
abbrev Cfg := TM0.Cfg (Alphabet m) (Control m)
local instance : Fintype m.core.σ := m.core.σFin
instance : Fintype (Control m) := inferInstance
instance : Inhabited (Control m) := ⟨(.inl (TapeSimulation.programme m).main,(TapeSimulation.programme m).initialState)⟩
abbrev RawNode := Label m ⊕ Option (Stmt m)

def selected (bit : Bool) (l : Label m) : Stmt m :=
  if bit then (TapeSimulation.programme m).alternate l else (TapeSimulation.programme m).core l
def Closed : RawNode m → Prop
  | .inl _ => True
  | .inr q => q ∈ TapeMicrostepBudget.primitiveControls m

theorem none_mem : (none : Option (Stmt m)) ∈ TapeMicrostepBudget.primitiveControls m := by
  classical
  apply Finset.mem_union_left
  simp [TapeMicrostepBudget.primitiveControls,TM1.stmts,Finset.mem_insertNone]

theorem subterm_mem (q r : Stmt m) (hq : some q ∈ TapeMicrostepBudget.primitiveControls m)
    (hr : r ∈ TM1.stmts₁ q) : some r ∈ TapeMicrostepBudget.primitiveControls m := by
  classical
  rcases Finset.mem_union.mp hq with h | h
  · exact Finset.mem_union_left _ (TM1.stmts_trans hr h)
  · exact Finset.mem_union_right _ (TM1.stmts_trans hr h)

theorem row_mem (bit : Bool) (l : Label m) : some (selected m bit l) ∈ TapeMicrostepBudget.primitiveControls m :=
  TapeMicrostepBudget.residual_control_mem m bit l 0 (TapeSimulation.programme m).initialState default

def narrowNode (n : RawNode m) (h : Closed m n) : Node m :=
  match n with
  | .inl l => .inl l
  | .inr q => .inr ⟨q,h⟩
def forgetNode : Node m → RawNode m
  | .inl l => .inl l
  | .inr q => .inr q.val
@[simp] theorem forget_narrow (n : RawNode m) (h : Closed m n) : forgetNode m (narrowNode m n h) = n := by cases n <;> rfl
theorem forgetNode_injective : Function.Injective (forgetNode m) := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr b => cases h
  | inr a => cases b with
    | inl b => cases h
    | inr b => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

/-- Exactly the trAux move/write calculation, with goto's actual target
label retained instead of its selected deterministic table body. -/
def aux (head : Alphabet m) : Stmt m → m.core.σ → (RawNode m × m.core.σ) × TM0.Stmt (Alphabet m)
  | .move d q,v => ((.inr (some q),v),.move d)
  | .write f q,v => ((.inr (some q),v),.write (f head v))
  | .load f q,v => aux head q (f head v)
  | .branch f q r,v => if f head v then aux head q v else aux head r v
  | .goto f,v => ((.inl (f head v),v),.write head)
  | .halt,v => ((.inr none,v),.write head)

theorem aux_closed (head : Alphabet m) (q : Stmt m) (v : m.core.σ)
    (hq : some q ∈ TapeMicrostepBudget.primitiveControls m) : Closed m (aux m head q v).1.1 := by
  classical
  induction q generalizing v with
  | move d q => exact subterm_mem m _ q hq (Finset.mem_insert_of_mem TM1.stmts₁_self)
  | write f q => exact subterm_mem m _ q hq (Finset.mem_insert_of_mem TM1.stmts₁_self)
  | load f q ih => exact ih (f head v) (subterm_mem m _ q hq (Finset.mem_insert_of_mem TM1.stmts₁_self))
  | branch f q r ihq ihr =>
      cases hf : f head v
      · simpa only [aux,hf,Bool.false_eq_true,ite_false] using
          ihr v (subterm_mem m _ r hq (Finset.mem_insert_of_mem (Finset.mem_union_right _ TM1.stmts₁_self)))
      · simpa only [aux,hf,ite_true] using
          ihq v (subterm_mem m _ q hq (Finset.mem_insert_of_mem (Finset.mem_union_left _ TM1.stmts₁_self)))
  | goto => trivial
  | halt => exact none_mem m

def opcode (head : Alphabet m) (q : Stmt m) (v : m.core.σ)
    (hq : some q ∈ TapeMicrostepBudget.primitiveControls m) : Control m × TM0.Stmt (Alphabet m) :=
  ((narrowNode m (aux m head q v).1.1 (aux_closed m head q v hq),(aux m head q v).1.2),(aux m head q v).2)

def table (bit : Bool) : TM0.Machine (Alphabet m) (Control m)
  | (.inl l,v),head => some (opcode m head (selected m bit l) v (row_mem m bit l))
  | (.inr ⟨none,_⟩,_),_ => none
  | (.inr ⟨some q,hq⟩,v),head => some (opcode m head q v hq)
def choose : Control m → Bool
  | (.inl l,_) => (TapeSimulation.programme m).choose l
  | (.inr _,_) => false
def step (token : Option Bool) (c : Cfg m) : Option (Cfg m) :=
  match token with
  | none => if choose m c.q then none else TM0.step (table m false) c
  | some bit => if choose m c.q then TM0.step (table m bit) c else none

theorem internal_no_choice (pc : PC m) (v : m.core.σ) (T : Tape (Alphabet m)) (bit : Bool) :
    step m (some bit) ⟨(.inr pc,v),T⟩ = none := rfl
theorem boundary_choice (l : Label m) (v : m.core.σ) :
    choose m (.inl l,v) = (TapeSimulation.programme m).choose l := rfl

structure Programme where
  core : TM0.Machine (Alphabet m) (Control m)
  alternate : TM0.Machine (Alphabet m) (Control m)
  split : Control m → Bool
  main : Control m
def programme : Programme m := ⟨table m false,table m true,choose m,default⟩

def runCfg (q : Stmt m) (hq : some q ∈ TapeMicrostepBudget.primitiveControls m)
    (v : m.core.σ) (T : Tape (Alphabet m)) : Cfg m := ⟨(.inr ⟨some q,hq⟩,v),T⟩
def haltCfg (v : m.core.σ) (T : Tape (Alphabet m)) : Cfg m := ⟨(.inr ⟨none,none_mem m⟩,v),T⟩
def embed (c : TapeSimulation.FiniteCfg m) : Cfg m :=
  match c.l with
  | some l => ⟨(.inl l,c.var),c.Tape⟩
  | none => haltCfg m c.var c.Tape
def Halted (c : Cfg m) : Prop := (forgetNode m c.q.1) = .inr none
def Boundary (c : Cfg m) : Prop :=
  match c.q.1 with | .inl _ => True | .inr q => q.val = none

theorem halt_no_edge (c : Cfg m) (h : Halted m c) (token : Option Bool) : step m token c = none := by
  rcases c with ⟨⟨node,v⟩,T⟩
  cases node with
  | inl l => cases h
  | inr pc => rcases pc with ⟨value,hpc⟩; cases value <;> cases token <;> simp_all [Halted,forgetNode,step,choose,table,TM0.step]
@[simp] theorem haltCfg_halted (v : m.core.σ) (T : Tape (Alphabet m)) : Halted m (haltCfg m v T) := rfl
theorem embed_halted (c : TapeSimulation.FiniteCfg m) (h : c.l = none) : Halted m (embed m c) := by
  simp [embed,Halted,haltCfg,forgetNode,h]
theorem embed_injective : Function.Injective (embed m) := by
  intro a b h
  rcases a with ⟨al,av,aT⟩; rcases b with ⟨bl,bv,bT⟩
  cases al <;> cases bl <;> simp_all [embed,haltCfg,TM0.Cfg.mk.injEq,TM1.Cfg.mk.injEq]

def applyOpcode (result : Control m × TM0.Stmt (Alphabet m)) (T : Tape (Alphabet m)) : Cfg m :=
  ⟨result.1,match result.2 with | .move d => T.move d | .write a => T.write a⟩
@[simp] theorem run_step (q : Stmt m) (hq) (v : m.core.σ) (T : Tape (Alphabet m)) :
    step m none (runCfg m q hq v T) = some (applyOpcode m (opcode m T.head q v hq) T) := by
  simp only [step,runCfg,choose,Bool.false_eq_true,ite_false,TM0.step,table]
  cases ho : opcode m T.head q v hq with
  | mk c op => cases op <;> rfl

/-- Erasure to the ACTUAL old deterministic opcodeMachine at any selected
row. This is a proved producer, not a caller simulation law. -/
def eraseControl (bit : Bool) (c : Control m) : Option (Stmt m) × m.core.σ :=
  (match c.1 with | .inl l => some (selected m bit l) | .inr q => q.val,c.2)
theorem opcode_erases (bit : Bool) (head : Alphabet m) (q : Stmt m) (v : m.core.σ) (hq) :
    (eraseControl m bit (opcode m head q v hq).1,(opcode m head q v hq).2) =
      TM1to0.trAux (TapeSimulation.finiteProgram m bit) head q v := by
  classical
  induction q generalizing v with
  | move => rfl
  | write => rfl
  | load f q ih => exact ih (f head v) (subterm_mem m _ q hq (Finset.mem_insert_of_mem TM1.stmts₁_self))
  | branch f q r ihq ihr =>
      cases hf : f head v
      · simpa only [opcode,aux,TM1to0.trAux,hf,Bool.false_eq_true,ite_false,Bool.cond_false] using
          ihr v (subterm_mem m _ r hq (Finset.mem_insert_of_mem (Finset.mem_union_right _ TM1.stmts₁_self)))
      · simpa only [opcode,aux,TM1to0.trAux,hf,ite_true,Bool.cond_true] using
          ihq v (subterm_mem m _ q hq (Finset.mem_insert_of_mem (Finset.mem_union_left _ TM1.stmts₁_self)))
  | goto => cases bit <;> rfl
  | halt => rfl

theorem table_erases (bit : Bool) (c : Control m) (head : Alphabet m) :
    ((table m bit c head).map fun result => (eraseControl m bit result.1,result.2)) =
      TapeSimulation.opcodeMachine m bit (eraseControl m bit c) head := by
  rcases c with ⟨node,v⟩
  cases node with
  | inl l => exact congrArg some (opcode_erases m bit head (selected m bit l) v (row_mem m bit l))
  | inr pc => rcases pc with ⟨value,hpc⟩; cases value with
    | none => rfl
    | some q => exact congrArg some (opcode_erases m bit head q v hpc)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveDispatcher.Program
