import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Program
import Mathlib.Tactic.FinCases

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Direct semantics of every original instruction and all
packet/control cases, with no simulator correctness hypothesis.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Program
open Turing Holant.Complexity
variable (m : BinaryMachine)

theorem word_update (word next : List Bool) :
    Function.update (fun _ : Unit => word) () next = (fun _ => next) := by
  funext key
  cases key
  rfl

theorem compile_stepAux (q : TM2.Stmt m.core.Γ m.core.Λ m.core.σ)
    (first second : Option Bool) (v : m.core.σ) (word : List Bool)
    (source : ∀ k, List (m.core.Γ k)) :
    TM2.stepAux (compileStmt m q) (first,second,v)
      (SumStacks.merge m.core.Γ (fun _ : Unit => word) source) =
        readyCfg m word (TM2.stepAux q v source) := by
  induction q generalizing first second v source with
  | push k f q ih =>
    simpa only [compileStmt,TM2.stepAux,SumStacks.merge,SumStacks.update_right] using
      ih first second v (Function.update source k (f v :: source k))
  | pop k f q ih =>
    simpa only [compileStmt,TM2.stepAux,SumStacks.merge,SumStacks.update_right,clear] using
      ih none none (f v (source k).head?) (Function.update source k (source k).tail)
  | peek k f q ih =>
    simpa only [compileStmt,TM2.stepAux,SumStacks.merge,clear] using
      ih none none (f v (source k).head?) source
  | load f q ih =>
    simpa only [compileStmt,TM2.stepAux,clear] using ih none none (f v) source
  | branch f q r hq hr =>
    cases h : f v <;> simp [compileStmt,TM2.stepAux,h,hq,hr]
  | goto f => rfl
  | halt => rfl

theorem read_first (word : List Bool) (c : m.Config) :
    (computer m).step (readyCfg m word c) =
      some (phaseCfg m 1 word.head? none word.tail c) := by
  simp [FinTM2.step,TM2.step,computer,program,readyCfg,phaseCfg,label,
    packet,TM2.stepAux,SumStacks.merge,SumStacks.update_left,word_update]

theorem read_second (first : Option Bool) (word : List Bool) (c : m.Config) :
    (computer m).step (phaseCfg m 1 first none word c) =
      some (phaseCfg m 2 first word.head? word.tail c) := by
  simp [FinTM2.step,TM2.step,computer,program,phaseCfg,label,
    packet,TM2.stepAux,SumStacks.merge,SumStacks.update_left,word_update]

/-- This is an equality about the actual interpreter's TM2 step. All invalid
packets/EOF/control combinations go to the fixed reject label. Every successful
case executes the very same source core/alternate statement, not a supplied
configuration-transforming function.
-/
theorem execute_packet (first second : Option Bool) (word : List Bool) (c : m.Config) :
    (computer m).step (phaseCfg m 2 first second word c) =
      some (match Packet.decode first second with
        | none => rejectedCfg m first second word c
        | some token => (m.step token c).elim
            (rejectedCfg m first second word c) (readyCfg m word)) := by
  cases hl : c.l with
  | none =>
    fin_cases first <;> fin_cases second <;>
      simp [FinTM2.step,TM2.step,computer,program,phaseCfg,rejectedCfg,readyCfg,
        label,reject,clear,ordinaryPacket,Packet.decode,BinaryMachine.step,hl,TM2.stepAux]
  | some l =>
    cases hs : m.split l <;> fin_cases first <;> fin_cases second <;>
      simp [FinTM2.step,TM2.step,computer,program,phaseCfg,rejectedCfg,label,reject,
        ordinaryPacket,splitPacket,Packet.decode,BinaryMachine.step,hl,hs,TM2.stepAux,
        compile_stepAux]

theorem read_two (first second : Bool) (word : List Bool) (c : m.Config) :
    (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[2]
      (some (readyCfg m (first :: second :: word) c)) =
      some (phaseCfg m 2 (some first) (some second) word c) := by
  simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,
    Option.bind_some,read_first,read_second,List.head?_cons,List.tail_cons]

theorem empty_packet (c : m.Config) :
    (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[3]
      (some (readyCfg m [] c)) = some (rejectedCfg m none none [] c) := by
  simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,Option.bind_some,
    read_first,read_second,execute_packet,List.head?_nil,List.tail_nil,Packet.first_eof]

theorem odd_packet (bit : Bool) (c : m.Config) :
    (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[3]
      (some (readyCfg m [bit] c)) = some (rejectedCfg m (some bit) none [] c) := by
  simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,Option.bind_some,
    read_first,read_second,execute_packet,List.head?_cons,List.tail_cons,List.head?_nil,
    List.tail_nil,Packet.second_eof]

/-- Exact three physical transitions for every genuine source edge. The sole
premise is the edge being simulated; no abstract macro/Computes/capacity law is
assumed. Source halt is simulated by consuming precisely the unique 00 packet.
-/
theorem round (token : Option Bool) (word : List Bool) (c d : m.Config)
    (h : m.step token c = some d) :
    (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[3]
      (some (readyCfg m (Packet.encode token ++ word) c)) = some (readyCfg m word d) := by
  change (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[3]
    (some (readyCfg m (Packet.first token :: Packet.second token :: word) c)) = _
  rw [Function.iterate_succ_apply',read_two,Option.bind_some,execute_packet]
  simp only [Packet.decode_encode,h,Option.elim_some]

theorem invalid_round (first second : Bool) (word : List Bool) (c : m.Config)
    (h : Packet.decode (some first) (some second) = none) :
    (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[3]
      (some (readyCfg m (first :: second :: word) c)) =
      some (rejectedCfg m (some first) (some second) word c) := by
  rw [Function.iterate_succ_apply',read_two,Option.bind_some,execute_packet,h]

theorem forbidden_round (token : Option Bool) (word : List Bool) (c : m.Config)
    (h : m.step token c = none) :
    (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[3]
      (some (readyCfg m (Packet.encode token ++ word) c)) =
      some (rejectedCfg m (some (Packet.first token)) (some (Packet.second token)) word c) := by
  change (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[3]
    (some (readyCfg m (Packet.first token :: Packet.second token :: word) c)) = _
  rw [Function.iterate_succ_apply',read_two,Option.bind_some,execute_packet]
  simp only [Packet.decode_encode,h,Option.elim_none]

/-- Return to the real source config after a complete valid physical trace. -/
theorem trace_run (tokens : List (Option Bool)) (word : List Bool) (c d : m.Config)
    (h : m.TraceValid tokens c d) :
    (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[3 * tokens.length]
      (some (readyCfg m (tokens.flatMap Packet.encode ++ word) c)) =
      some (readyCfg m word d) := by
  induction tokens generalizing c with
  | nil =>
    have hd : c = d := h
    subst d
    rfl
  | cons token tokens ih =>
    obtain ⟨next,hs,ht⟩ := h
    rw [List.length_cons,Nat.mul_succ,Function.iterate_add_apply]
    simp only [List.flatMap_cons,List.append_assoc]
    rw [round m token (tokens.flatMap Packet.encode ++ word) c next hs]
    exact ih next ht

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Program
