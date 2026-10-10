import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Semantics

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Consumers of the original interpreter and cleaner.
The clock is a real unary tape. Its token is consumed inside the original first
packet-read transition; the original second/execute transitions are unchanged.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
open Turing Holant.Complexity BinaryCompose
open scoped BigOperators
variable (m : BinaryMachine) (T : Polynomial ℕ) (acceptControl : m.core.σ → Bool)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k
local instance (k : Stack m T) : Fintype (Alphabet m T k) :=
  (deterministic m T (fun _ => false)).alphabets k

def embedOldCfg (prep : (clock T).K → List Bool)
    (scratch : ∀ k, List (ExtraAlphabet m k)) (c : (Reverse.Program.computer m).Cfg) :
    (computer m T acceptControl).Cfg :=
  HeterogeneousSum.rightCfg (fun _ : (clock T).K => Bool) (InnerAlphabet m)
    (oldStates m T) (interpreter m T) none prep
    (HeterogeneousSum.rightCfg (ExtraAlphabet m) (Reverse.Program.Alphabet m)
      ⟨id,id,fun _ => rfl⟩ id none scratch c)

def phaseCfg (count : ℕ) (phase : Fin 3) (first second : Option Bool)
    (word : List Bool) (c : m.Config) : (computer m T acceptControl).Cfg :=
  embedOldCfg m T acceptControl (wordTape (clock T).output (List.replicate count true))
    (extras m [] [] []) (Reverse.Program.phaseCfg m phase first second word c)

def readyCfg (count : ℕ) (word : List Bool) (c : m.Config) :
    (computer m T acceptControl).Cfg := phaseCfg m T acceptControl count 0 none none word c

def rejectedCfg (count : ℕ) (first second : Option Bool) (word : List Bool) (c : m.Config) :
    (computer m T acceptControl).Cfg :=
  embedOldCfg m T acceptControl (wordTape (clock T).output (List.replicate count true))
    (extras m [] [] []) (Reverse.Program.rejectedCfg m first second word c)

def cleanupCfg (verdict : Bool) (S : ∀ k, List (Alphabet m T k)) :
    (computer m T acceptControl).Cfg :=
  HeterogeneousSum.restateCfg (Alphabet m T) (cleanupStates m T) (clean m T) none
    (Cleanup.cfg (Alphabet m T) (raw m T) (raw m T) Sum.inr 0 verdict S)

theorem oldStatement_stepAux (q : (Reverse.Program.computer m).Stmt)
    (v : Reverse.Program.State m) (prep : (clock T).K → List Bool)
    (scratch : ∀ k, List (ExtraAlphabet m k))
    (S : ∀ k, List (Reverse.Program.Alphabet m k)) :
    TM2.stepAux (oldStatement m T q) ((oldStates m T).put v)
      (SumStacks.merge (InnerAlphabet m) prep
        (HeterogeneousSum.merge (ExtraAlphabet m) (Reverse.Program.Alphabet m) scratch S)) =
      embedOldCfg m T acceptControl prep scratch (TM2.stepAux q v S) := by
  unfold oldStatement
  change TM2.stepAux _ _ (HeterogeneousSum.merge (fun _ : (clock T).K => Bool) (InnerAlphabet m) prep _) = _
  rw [HeterogeneousSum.right_stepAux]
  have hi := HeterogeneousSum.right_stepAux (ExtraAlphabet m) (Reverse.Program.Alphabet m)
    (⟨id, id, fun _ => rfl⟩ : StateEmbedding (Reverse.Program.State m) (Reverse.Program.State m))
    id none q v scratch S
  simp only [id_eq] at hi
  rw [hi]
  rfl

theorem clock_terminal (word : List (m.core.Γ m.core.k₀)) (bits : List Bool) (count : ℕ) :
    clockCfg m T acceptControl word bits
      (haltList (clock T).computer (List.replicate count true)) =
        readyCfg m T acceptControl count bits (initList m.core word) := by
  rw [Machine.halt_eq]
  rfl

theorem first_with_clock (count : ℕ) (word : List Bool) (c : m.Config) :
    (computer m T acceptControl).step (readyCfg m T acceptControl (count+1) word c) =
      some (phaseCfg m T acceptControl count 1 word.head? none word.tail c) := by
  simp [FinTM2.step,TM2.step,computer,program,readyCfg,phaseCfg,embedOldCfg,
    interpreter,Reverse.Program.phaseCfg,Reverse.Program.label,Reverse.Program.program,
    Reverse.Program.packet,oldStatement,HeterogeneousSum.rightStmt,
    HeterogeneousSum.rightCfg,HeterogeneousSum.merge,HeterogeneousSum.update_right,
    SumStacks.merge,SumStacks.update_left,SumStacks.update_right,oldStates,oldState,
    setBit,counter,TM2.stepAux,wordTape,Function.update_idem,List.replicate_succ,
    Reverse.Program.word_update]
  funext k
  cases k with
  | inl k => simp [HeterogeneousSum.merge, Function.update_idem]
  | inr k =>
    cases k with
    | inl k => simp [HeterogeneousSum.merge]
    | inr k =>
      cases k with
      | inl u => cases u; simp [HeterogeneousSum.merge, SumStacks.merge]
      | inr k => simp [HeterogeneousSum.merge, SumStacks.merge]

theorem phase_step (count : ℕ) (phase : Fin 3) (hne : phase ≠ 0)
    (first second : Option Bool) (word : List Bool) (c : m.Config)
    (d : (Reverse.Program.computer m).Cfg)
    (h : (Reverse.Program.computer m).step
      (Reverse.Program.phaseCfg m phase first second word c) = some d) :
    (computer m T acceptControl).step (phaseCfg m T acceptControl count phase first second word c) =
      some (embedOldCfg m T acceptControl
        (wordTape (clock T).output (List.replicate count true)) (extras m [] [] []) d) := by
  have hd : TM2.stepAux (Reverse.Program.program m (Reverse.Program.label m c.l phase))
      (first,second,c.var) (SumStacks.merge m.core.Γ (fun _ : Unit => word) c.stk) = d :=
    Option.some.inj h
  subst d
  simp only [FinTM2.step,TM2.step,computer,phaseCfg,embedOldCfg,
    HeterogeneousSum.rightCfg,Reverse.Program.phaseCfg,Option.elim_some,Option.map_some,
    interpreter,Reverse.Program.label,program,hne,ite_false,oldStatement_stepAux, id_eq]
  convert congrArg some (oldStatement_stepAux m T acceptControl
    (Reverse.Program.program m (Reverse.Program.label m c.l phase))
    (first, second, c.var) (wordTape (clock T).output (List.replicate count true))
    (extras m [] [] []) (SumStacks.merge m.core.Γ (fun _ => word) c.stk)) using 1 <;> rfl

theorem second_with_clock (count : ℕ) (first : Option Bool) (word : List Bool) (c : m.Config) :
    (computer m T acceptControl).step (phaseCfg m T acceptControl count 1 first none word c) =
      some (phaseCfg m T acceptControl count 2 first word.head? word.tail c) := by
  exact phase_step m T acceptControl count 1 (by decide) first none word c _
    (Reverse.Program.read_second m first word c)

theorem execute_with_clock (count : ℕ) (first second : Option Bool)
    (word : List Bool) (c : m.Config) :
    (computer m T acceptControl).step (phaseCfg m T acceptControl count 2 first second word c) =
      some (match Packet.decode first second with
        | none => rejectedCfg m T acceptControl count first second word c
        | some token => (m.step token c).elim
            (rejectedCfg m T acceptControl count first second word c)
            (readyCfg m T acceptControl count word)) := by
  have h := phase_step m T acceptControl count 2 (by decide) first second word c _
    (Reverse.Program.execute_packet m first second word c)
  cases hd : Packet.decode first second with
  | none => simpa only [hd,rejectedCfg] using h
  | some token =>
    cases hs : m.step token c <;>
      simpa only [hd,hs,Option.elim_none,Option.elim_some,rejectedCfg,readyCfg,
        phaseCfg,Reverse.Program.readyCfg] using h

theorem guarded_round (count : ℕ) (token : Option Bool) (word : List Bool)
    (c d : m.Config) (h : m.step token c = some d) :
    (fun p => p.bind (computer m T acceptControl).step)^[3]
      (some (readyCfg m T acceptControl (count+1) (Packet.encode token++word) c)) =
        some (readyCfg m T acceptControl count word d) := by
  change (fun p => p.bind (computer m T acceptControl).step)^[3]
    (some (readyCfg m T acceptControl (count+1)
      (Packet.first token::Packet.second token::word) c)) = _
  simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,Option.bind_some,
    first_with_clock,second_with_clock,execute_with_clock,List.head?_cons,List.tail_cons,
    Packet.decode_encode,h,Option.elim_some]

theorem guarded_trace (tokens : List (Option Bool)) (word : List Bool)
    (c d : m.Config) (h : m.TraceValid tokens c d) :
    (fun p => p.bind (computer m T acceptControl).step)^[3*tokens.length]
      (some (readyCfg m T acceptControl tokens.length (tokens.flatMap Packet.encode++word) c)) =
        some (readyCfg m T acceptControl 0 word d) := by
  induction tokens generalizing c with
  | nil =>
    have hd : c = d := h
    subst d
    rfl
  | cons token tokens ih =>
    obtain ⟨next,hs,ht⟩ := h
    rw [List.length_cons,Nat.mul_succ,Function.iterate_add_apply]
    simp only [List.flatMap_cons,List.append_assoc]
    rw [guarded_round m T acceptControl tokens.length token
      (tokens.flatMap Packet.encode++word) c next hs]
    exact ih next ht

def terminalVerdict (word : List Bool) (c : m.Config) : Bool :=
  word.isEmpty && c.l.isNone && acceptControl c.var

/-- A simultaneous real clock/packet EOF check. Any remaining byte, including
an otherwise canonical 00 padding packet, makes the returned verdict false. -/
theorem clock_eof (word : List Bool) (c : m.Config) :
    (computer m T acceptControl).step (readyCfg m T acceptControl 0 word c) =
      some (cleanupCfg m T acceptControl (terminalVerdict m acceptControl word c)
        (readyCfg m T acceptControl 0 word c).stk) := by
  simp [FinTM2.step,TM2.step,computer,program,readyCfg,phaseCfg,embedOldCfg,
    HeterogeneousSum.rightCfg,interpreter,Reverse.Program.phaseCfg,Reverse.Program.label,
    counter,packet,wordTape,SumStacks.merge,HeterogeneousSum.merge,TM2.stepAux,
    setBit,oldStates,oldState,finish,cleanupCfg,HeterogeneousSum.restateCfg,Cleanup.cfg,
    terminalVerdict,List.isEmpty,Function.update_eq_self]
  cases word <;> rfl

theorem reject_cleanup (count : ℕ) (first second : Option Bool)
    (word : List Bool) (c : m.Config) :
    (computer m T acceptControl).step (rejectedCfg m T acceptControl count first second word c) =
      some (cleanupCfg m T acceptControl false
        (rejectedCfg m T acceptControl count first second word c).stk) := by
  simp [FinTM2.step,TM2.step,computer,program,rejectedCfg,embedOldCfg,
    HeterogeneousSum.rightCfg,interpreter,Reverse.Program.rejectedCfg,Reverse.Program.reject,
    TM2.stepAux,finish,cleanupCfg,HeterogeneousSum.restateCfg,Cleanup.cfg]

theorem cleanup_halt (verdict : Bool) :
    HeterogeneousSum.restateCfg (Alphabet m T) (cleanupStates m T) (clean m T) none
      (haltList (Cleanup.computer (Alphabet m T) (raw m T) (raw m T) Sum.inr)
        [Sum.inr verdict]) = haltList (computer m T acceptControl) [Sum.inr verdict] := by
  simp only [HeterogeneousSum.restateCfg,haltList,Option.elim_none,computer,Cleanup.computer,
    cleanupStates,setVerdict,setSeen,initial]

/-- Every tape is physically popped by the same finite program before halt;
no premise says a working tape is empty or its contents are known. -/
theorem cleanup_run (verdict : Bool) (S : ∀ k, List (Alphabet m T k)) :
    ∃ t, t ≤ Fintype.card (Stack m T)*((∑ k, (S k).length)+1)+1 ∧
      (fun p => p.bind (computer m T acceptControl).step)^[t]
        (some (cleanupCfg m T acceptControl verdict S)) =
          some (haltList (computer m T acceptControl) [Sum.inr verdict]) := by
  obtain ⟨t,ht,hr⟩ := Cleanup.clean_run (Alphabet m T) (raw m T) (raw m T) Sum.inr verdict S
  refine ⟨t,ht,?_⟩
  have h := HeterogeneousSum.restate_run (Alphabet m T) (cleanupStates m T) (clean m T) none
    (Cleanup.program (Alphabet m T) (raw m T) Sum.inr) (program m T acceptControl)
    (fun _ => rfl) t _ _ hr
  have h' := h.trans (congrArg some (cleanup_halt m T acceptControl verdict))
  convert h' using 1 <;> rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
