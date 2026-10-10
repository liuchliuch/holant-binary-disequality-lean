import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveDispatcher.Program

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Measured actual TM0 transcripts of the installed rows.
Selection and goto are not stuttering proof-driver edges: the first opcode
consumes the source token; goto/halt each perform a real write-self step. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveDispatcher.Runs
open Turing Computability Holant.Complexity
open Program
variable (m : BinaryMachine)

def Trace : List (Option Bool) → Cfg m → Cfg m → Prop
  | [],a,b => a = b
  | token::tokens,a,b => ∃ next, step m token a = some next ∧ Trace tokens next b

theorem append (xs ys : List (Option Bool)) (a mid b : Cfg m)
    (hx : Trace m xs a mid) (hy : Trace m ys mid b) : Trace m (xs++ys) a b := by
  induction xs generalizing a with
  | nil => change a = mid at hx; subst a; exact hy
  | cons token tokens ih => obtain ⟨next,hs,hr⟩ := hx; exact ⟨next,hs,ih next hr⟩

theorem replace_first (n : ℕ) (a a' b : Cfg m) (hn : 0 < n)
    (he : step m none a = step m none a')
    (h : Trace m (List.replicate n none) a' b) : Trace m (List.replicate n none) a b := by
  cases n with
  | zero => omega
  | succ n =>
      simp only [List.replicate_succ] at h ⊢
      obtain ⟨next,hs,hr⟩ := h
      exact ⟨next,he.trans hs,hr⟩

/-- Exact syntax-generated physical transcript, at least one actual opcode.
Its fee is bounded by the already charged rowOperations, not by Reaches or
an independently supplied interpreter clock. -/
theorem statement (q : Stmt m) (hq : some q ∈ TapeMicrostepBudget.primitiveControls m)
    (v : m.core.σ) (T : Tape (Alphabet m)) :
    ∃ n : ℕ, 0 < n ∧ Trace m (List.replicate n none) (runCfg m q hq v T)
      (embed m (TM1.stepAux q v T)) ∧ n ≤ TapeSimulation.rowOperations m q v T := by
  classical
  induction q generalizing v T with
  | move d q ih =>
      have hchild := subterm_mem m _ q hq (Finset.mem_insert_of_mem TM1.stmts₁_self)
      obtain ⟨n,hn,hr,hb⟩ := ih (hq := hchild) (v := v) (T := T.move d)
      refine ⟨n+1,by omega,?_,?_⟩
      · simp only [List.replicate_succ]
        exact ⟨runCfg m q hchild v (T.move d),rfl,hr⟩
      · simpa [TapeSimulation.rowOperations,Nat.add_comm] using Nat.add_le_add_right hb 1
  | write f q ih =>
      have hchild := subterm_mem m _ q hq (Finset.mem_insert_of_mem TM1.stmts₁_self)
      obtain ⟨n,hn,hr,hb⟩ := ih (hq := hchild) (v := v) (T := T.write (f T.head v))
      refine ⟨n+1,by omega,?_,?_⟩
      · simp only [List.replicate_succ]
        exact ⟨runCfg m q hchild v (T.write (f T.head v)),rfl,hr⟩
      · simpa [TapeSimulation.rowOperations,Nat.add_comm] using Nat.add_le_add_right hb 1
  | load f q ih =>
      have hchild := subterm_mem m _ q hq (Finset.mem_insert_of_mem TM1.stmts₁_self)
      obtain ⟨n,hn,hr,hb⟩ := ih (hq := hchild) (v := f T.head v) (T := T)
      have he : step m none (runCfg m (.load f q) hq v T) =
          step m none (runCfg m q hchild (f T.head v) T) := rfl
      exact ⟨n,hn,replace_first m n _ _ _ hn he hr,hb.trans (by simp [TapeSimulation.rowOperations])⟩
  | branch f q r ihq ihr =>
      cases hf : f T.head v
      · have hchild := subterm_mem m _ r hq (Finset.mem_insert_of_mem (Finset.mem_union_right _ TM1.stmts₁_self))
        obtain ⟨n,hn,hr,hb⟩ := ihr (hq := hchild) (v := v) (T := T)
        have he : step m none (runCfg m (.branch f q r) hq v T) = step m none (runCfg m r hchild v T) := by
          rw [run_step,run_step]
          simp [opcode,aux,hf]
        refine ⟨n,hn,?_,?_⟩
        · simpa only [TM1.stepAux,hf,Bool.cond_false] using replace_first m n _ _ _ hn he hr
        · simpa [TapeSimulation.rowOperations,hf] using hb.trans (Nat.le_add_left _ 1)
      · have hchild := subterm_mem m _ q hq (Finset.mem_insert_of_mem (Finset.mem_union_left _ TM1.stmts₁_self))
        obtain ⟨n,hn,hr,hb⟩ := ihq (hq := hchild) (v := v) (T := T)
        have he : step m none (runCfg m (.branch f q r) hq v T) = step m none (runCfg m q hchild v T) := by
          rw [run_step,run_step]
          simp [opcode,aux,hf]
        refine ⟨n,hn,?_,?_⟩
        · simpa only [TM1.stepAux,hf,Bool.cond_true] using replace_first m n _ _ _ hn he hr
        · simpa [TapeSimulation.rowOperations,hf] using hb.trans (Nat.le_add_left _ 1)
  | goto f =>
      refine ⟨1,by omega,?_,le_rfl⟩
      refine ⟨embed m (TM1.stepAux (.goto f) v T),?_,rfl⟩
      simp [step,choose,table,TM0.step,runCfg,opcode,aux,narrowNode,embed,TM1.stepAux,Tape.write_self]
  | halt =>
      refine ⟨1,by omega,?_,le_rfl⟩
      refine ⟨haltCfg m v T,?_,rfl⟩
      simp [step,choose,table,TM0.step,runCfg,opcode,aux,narrowNode,embed,haltCfg,TM1.stepAux,Tape.write_self]

theorem entry (token : Option Bool) (c d : TapeSimulation.FiniteCfg m)
    (hs : TapeSimulation.finiteStep m token c = some d) :
    ∃ instructions, Trace m instructions (embed m c) (embed m d) ∧
      instructions.filterMap id = token.toList ∧
      instructions.length ≤ TapeSimulation.transitionOperations m token c := by
  cases hl : c.l with
  | none => simp [TapeSimulation.finiteStep,hl] at hs
  | some l =>
      have chosen (bit : Bool)
          (hd : TM1.stepAux (selected m bit l) c.var c.Tape = d)
          (he : step m token (embed m c) = step m none (runCfg m (selected m bit l) (row_mem m bit l) c.var c.Tape))
          (hcost : TapeSimulation.transitionOperations m token c =
            TapeSimulation.rowOperations m (selected m bit l) c.var c.Tape) :
          ∃ instructions, Trace m instructions (embed m c) (embed m d) ∧
            instructions.filterMap id = token.toList ∧
            instructions.length ≤ TapeSimulation.transitionOperations m token c := by
        obtain ⟨n,hn,hr,hb⟩ := statement m (selected m bit l) (row_mem m bit l) c.var c.Tape
        rw [hd] at hr
        cases n with
        | zero => omega
        | succ n =>
            simp only [List.replicate_succ] at hr
            obtain ⟨next,hfirst,hrest⟩ := hr
            refine ⟨token::List.replicate n none,⟨next,he.trans hfirst,hrest⟩,?_,?_⟩
            · cases token <;> simp
            · simpa only [List.length_cons,List.length_replicate,hcost] using hb
      cases token with
      | none =>
          cases hc : (TapeSimulation.programme m).choose l
          · have hd := Option.some.inj (by simpa [TapeSimulation.finiteStep,hl,hc,selected] using hs)
            apply chosen false hd
            · simp [step,embed,choose,table,TM0.step,runCfg,hl,hc]
            · simp [TapeSimulation.transitionOperations,hl,hc,selected]
          · simp [TapeSimulation.finiteStep,hl,hc] at hs
      | some bit =>
          cases hc : (TapeSimulation.programme m).choose l
          · simp [TapeSimulation.finiteStep,hl,hc] at hs
          · have hd := Option.some.inj (by simpa [TapeSimulation.finiteStep,hl,hc,selected] using hs)
            apply chosen bit hd
            · simp [step,embed,choose,table,TM0.step,runCfg,hl,hc]
            · simp [TapeSimulation.transitionOperations,hl,hc,selected]

/-- Actual transcript concatenation. Each source row keeps its original
choice exactly once; internal opcode tokens are uniquely None. -/
theorem expand (tokens : List (Option Bool)) (a b : TapeSimulation.FiniteCfg m)
    (h : TapeSimulation.InstructionTrace m tokens a b) :
    ∃ instructions, Trace m instructions (embed m a) (embed m b) ∧
      instructions.filterMap id = tokens.filterMap id ∧
      instructions.length ≤ TapeSimulation.instructionOperations m tokens a := by
  induction tokens generalizing a with
  | nil => change a = b at h; subst a; exact ⟨[],rfl,rfl,by simp [TapeSimulation.instructionOperations]⟩
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := h
      obtain ⟨first,hfirst,hlog,hfee⟩ := entry m token a next hs
      obtain ⟨rest,hrest,hlogs,hbound⟩ := ih next hr
      refine ⟨first++rest,append m _ _ _ _ _ hfirst hrest,?_,?_⟩
      · rw [List.filterMap_append,hlog,hlogs]
        cases token <;> rfl
      · have hc := Nat.add_le_add hfee hbound
        simpa [List.length_append,TapeSimulation.instructionOperations,hs] using hc

theorem edge_log (token other : Option Bool) (a b c : Cfg m) (left right : List Bool)
    (hb : step m token a = some b) (hc : step m other a = some c)
    (hlog : token.toList++left = other.toList++right) : token = other ∧ b = c ∧ left = right := by
  cases hs : choose m a.q
  · cases token with
    | some bit => simp [step,hs] at hb
    | none => cases other with
      | some bit => simp [step,hs] at hc
      | none => exact ⟨rfl,Option.some.inj (hb.symm.trans hc),hlog⟩
  · cases token with
    | none => simp [step,hs] at hb
    | some bit => cases other with
      | none => simp [step,hs] at hc
      | some otherBit =>
          have he : bit = otherBit ∧ left = right := List.cons.inj hlog
          obtain ⟨rfl, htail⟩ := he
          exact ⟨rfl,Option.some.inj (hb.symm.trans hc),htail⟩

theorem prefixTrace (xs ys : List (Option Bool)) (a b c : Cfg m)
    (hx : Trace m xs a b) (hy : Trace m ys a c) (hc : Halted m c)
    (left right : List Bool) (hlog : xs.filterMap id++left = ys.filterMap id++right) :
    ∃ rest, ys = xs++rest ∧ Trace m rest b c := by
  induction xs generalizing ys a with
  | nil => change a = b at hx; subst a; exact ⟨ys,rfl,hy⟩
  | cons token tokens ih =>
      obtain ⟨next,hs,hr⟩ := hx
      cases ys with
      | nil => change a = c at hy; subst a; rw [halt_no_edge m c hc token] at hs; cases hs
      | cons other others =>
          obtain ⟨next',ht,hr'⟩ := hy
          have hl : token.toList++(tokens.filterMap id++left) = other.toList++(others.filterMap id++right) := by
            cases token <;> cases other <;> exact hlog
          obtain ⟨he,hm,hlogs⟩ := edge_log m token other a next next' _ _ hs ht hl
          subst other
          subst next'
          obtain ⟨rest,hcut,htrace⟩ := ih others next hr hr' hlogs
          exact ⟨rest,by simp only [hcut,List.cons_append],htrace⟩

theorem halted_trace (xs : List (Option Bool)) (a b : Cfg m) (ha : Halted m a) (h : Trace m xs a b) :
    xs = [] ∧ a = b := by
  cases xs with
  | nil => exact ⟨rfl,h⟩
  | cons token tokens => obtain ⟨next,hs,hr⟩ := h; rw [halt_no_edge m a ha token] at hs; cases hs

theorem unique (xs ys : List (Option Bool)) (a b c : Cfg m)
    (hx : Trace m xs a b) (hy : Trace m ys a c) (hb : Halted m b) (hc : Halted m c)
    (hlog : xs.filterMap id = ys.filterMap id) : xs = ys ∧ b = c := by
  obtain ⟨rest,hcut,hrest⟩ := prefixTrace m xs ys a b c hx hy hc [] [] (by simpa using hlog)
  obtain ⟨hz,he⟩ := halted_trace m rest b c hb hrest
  exact ⟨by simpa [hz] using hcut.symm,he⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.NDPrimitiveDispatcher.Runs
