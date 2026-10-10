import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.NativeFinish

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Operational consumer of the installed NativeFinish
tables. A raw preparation prefix, the original split-token trace and one final
None edge form the complete accepting trace. The extra edge also covers early
source halt: its former None padding executes the decoder once, then holds.
Neither a decoder verdict, a simulation law, nor a clock/count law is supplied.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.NativeExecution
open Turing Computability Holant.Complexity BinaryCompose
namespace TP
export Reverse.TapeAcceptance.Program
  (liftCfg lift_init machine computer clear statement statement_stepAux acceptControl endpoint_accepts_iff)
end TP
namespace HS
export Reverse.Staging.HeterogeneousSum (restateCfg restate_stepAux)
end HS
variable (m : BinaryMachine) (trueSymbol : m.core.Γ m.core.k₁)
    (inputAlphabet : m.core.Γ m.core.k₀ ≃ Bool)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : DecidableEq (m.core.Γ m.core.k₁) := Classical.decEq _
abbrev native := NativeFinish.machine m trueSymbol inputAlphabet
abbrev observed := Output.observed m trueSymbol
abbrev base := NativeFinish.old m trueSymbol inputAlphabet

/-- Only a proof representation; the running machine is NativeFinish.program. -/
def entry (c : m.Config) : (native m trueSymbol inputAlphabet).Config :=
  NativeFinish.cfg m trueSymbol inputAlphabet
    (NativeInput.sourceCfg (observed m trueSymbol) inputAlphabet
      (Compiler.cfg (observed m trueSymbol) (TP.liftCfg m trueSymbol c)))

theorem entry_active (c : m.Config) :
    (entry m trueSymbol inputAlphabet c).l.isSome = true := by
  cases hl : c.l <;>
    simp [entry,NativeFinish.cfg,HS.restateCfg,NativeInput.sourceCfg,embedCfg,
      Compiler.cfg,TP.liftCfg,hl,NativeFinish.label]

theorem base_split (l : (base m trueSymbol inputAlphabet).core.Λ) :
    (native m trueSymbol inputAlphabet).split (NativeFinish.label m trueSymbol l) =
      (base m trueSymbol inputAlphabet).split l := by
  cases l <;> rfl

/-- Same actual selected statement; halt is redirected, not executed for free. -/
theorem base_statement (b : Bool) (l : (base m trueSymbol inputAlphabet).core.Λ)
    (v : (base m trueSymbol inputAlphabet).core.σ)
    (S : (base m trueSymbol inputAlphabet).core.K → List Bool) :
    TM2.stepAux (NativeFinish.program m trueSymbol inputAlphabet b (NativeFinish.label m trueSymbol l)) v S =
      NativeFinish.cfg m trueSymbol inputAlphabet
        (TM2.stepAux (NativeInput.program (observed m trueSymbol) inputAlphabet b l) v S) := by
  rw [NativeFinish.program_at_label]
  exact Reverse.Staging.HeterogeneousSum.restate_stepAux _ _ _ _ _ _ _

theorem base_step_active (token : Option Bool) (c : (base m trueSymbol inputAlphabet).Config)
    (hc : c.l.isSome = true) :
    (native m trueSymbol inputAlphabet).step token (NativeFinish.cfg m trueSymbol inputAlphabet c) =
      ((base m trueSymbol inputAlphabet).step token c).map
        (NativeFinish.cfg m trueSymbol inputAlphabet) := by
  have hlabel : (NativeFinish.cfg m trueSymbol inputAlphabet c).l =
      c.l.elim (some (NativeFinish.decoderLabel m)) (fun l => some (NativeFinish.label m trueSymbol l)) := rfl
  have hvar : (NativeFinish.cfg m trueSymbol inputAlphabet c).var = c.var := rfl
  have hstk : (NativeFinish.cfg m trueSymbol inputAlphabet c).stk = c.stk := rfl
  cases hl : c.l with
  | none => simp [hl] at hc
  | some l =>
    have hs : (native m trueSymbol inputAlphabet).split (NativeFinish.label m trueSymbol l) =
        (base m trueSymbol inputAlphabet).split l := base_split m trueSymbol inputAlphabet l
    cases l with
    | inl i =>
      cases token with
      | none =>
        simp only [BinaryMachine.step,hlabel,hl,Option.elim_some,NativeFinish.label,
          Bool.false_eq_true,ite_false,Option.map_some,hvar,hstk]
        exact congrArg some (base_statement m trueSymbol inputAlphabet false (.inl i) c.var c.stk)
      | some bit => simp only [BinaryMachine.step,hlabel,hl,Option.elim_some,NativeFinish.label,
          Bool.false_eq_true,ite_false,Option.map_none]
    | inr l =>
      cases token with
      | none => cases hsplit : m.split l <;>
          simp only [BinaryMachine.step,hlabel,hl,Option.elim_some,NativeFinish.label,hsplit,
            Bool.false_eq_true,ite_false,ite_true,Option.map_none,Option.map_some,hvar,hstk] <;>
          exact congrArg some (base_statement m trueSymbol inputAlphabet false (.inr l) c.var c.stk)
      | some bit => cases bit <;> cases hsplit : m.split l <;>
          simp only [BinaryMachine.step,hlabel,hl,Option.elim_some,NativeFinish.label,hsplit,
            Bool.false_eq_true,ite_false,ite_true,Option.map_none,Option.map_some,hvar,hstk] <;>
          first
          | exact congrArg some (base_statement m trueSymbol inputAlphabet false (.inr l) c.var c.stk)
          | exact congrArg some (base_statement m trueSymbol inputAlphabet true (.inr l) c.var c.stk)

theorem base_advance_active (log : List Bool) (c : (base m trueSymbol inputAlphabet).Config)
    (hc : c.l.isSome = true) :
    (native m trueSymbol inputAlphabet).advance (log,NativeFinish.cfg m trueSymbol inputAlphabet c) =
      ((base m trueSymbol inputAlphabet).advance (log,c)).map
        (fun s => (s.1,NativeFinish.cfg m trueSymbol inputAlphabet s.2)) := by
  have hlabel : (NativeFinish.cfg m trueSymbol inputAlphabet c).l =
      c.l.elim (some (NativeFinish.decoderLabel m)) (fun l => some (NativeFinish.label m trueSymbol l)) := rfl
  cases hl : c.l with
  | none => simp [hl] at hc
  | some l =>
    have hstep (token : Option Bool) := base_step_active m trueSymbol inputAlphabet token c hc
    cases l with
    | inl i =>
      simp only [BinaryMachine.advance,hlabel,hl,Option.elim_some,NativeFinish.label,
        Bool.false_eq_true,ite_false,hstep,Option.map_map,Function.comp_def]
    | inr l =>
      cases hs : m.split l with
      | false => simp only [BinaryMachine.advance,hlabel,hl,Option.elim_some,NativeFinish.label,hs,
          Bool.false_eq_true,ite_false,hstep,Option.map_map,Function.comp_def]
      | true => cases log with
        | nil => simp only [BinaryMachine.advance,hlabel,hl,Option.elim_some,NativeFinish.label,hs,
            ite_true,Option.map_none]
        | cons bit rest => simp only [BinaryMachine.advance,hlabel,hl,Option.elim_some,NativeFinish.label,hs,
            ite_true,hstep,Option.map_map,Function.comp_def]

/-- The old physical preparation run cannot have halted before its internally
produced active endpoint. This transports that run with its original log. -/
theorem base_run_active (n : ℕ) (start finish : List Bool × (base m trueSymbol inputAlphabet).Config)
    (hr : (base m trueSymbol inputAlphabet).run n start = some finish)
    (hf : finish.2.l.isSome = true) :
    (native m trueSymbol inputAlphabet).run n
      (start.1,NativeFinish.cfg m trueSymbol inputAlphabet start.2) =
        some (finish.1,NativeFinish.cfg m trueSymbol inputAlphabet finish.2) := by
  induction n generalizing start with
  | zero => have h := Option.some.inj hr; subst start; rfl
  | succ n ih =>
    cases hl : start.2.l with
    | none =>
      have h := (base m trueSymbol inputAlphabet).run_halt (n+1) start.1 start.2 hl
      have he := Option.some.inj (h.symm.trans hr)
      rw [← he,hl] at hf
      simp at hf
    | some l =>
      have ha : start.2.l.isSome = true := by simp [hl]
      cases hs : (base m trueSymbol inputAlphabet).advance start with
      | none => simp [BinaryMachine.run,hs] at hr
      | some next =>
        have hn : (base m trueSymbol inputAlphabet).run n next = some finish := by
          simpa only [BinaryMachine.run,hs,Option.bind_some] using hr
        rw [BinaryMachine.run,base_advance_active m trueSymbol inputAlphabet start.1 start.2 ha,
          hs,Option.map_some,Option.bind_some]
        exact ih next hn

theorem prepare_run (word log : List Bool) :
    (native m trueSymbol inputAlphabet).run
      (NativeInput.steps (observed m trueSymbol) word.length)
      (log,initList (native m trueSymbol inputAlphabet).core word) =
        some (log,entry m trueSymbol inputAlphabet
          (initList m.core (word.map inputAlphabet.symm))) := by
  have hr := NativeInput.prepare (observed m trueSymbol) inputAlphabet word log
  have ht := base_run_active m trueSymbol inputAlphabet _ _ _ hr rfl
  have hi : NativeFinish.cfg m trueSymbol inputAlphabet
      (initList (base m trueSymbol inputAlphabet).core word) =
      initList (native m trueSymbol inputAlphabet).core word := rfl
  rw [hi] at ht
  simpa only [entry,TP.lift_init] using ht

/-- Compiler, source-stack embedding and label restatement, on the same
original instruction. Each equality is consumed from the actual old producer. -/
theorem source_step_active (token : Option Bool) (c : m.Config)
    (hc : c.l.isSome = true) :
    (native m trueSymbol inputAlphabet).step token (entry m trueSymbol inputAlphabet c) =
      (m.step token c).map (entry m trueSymbol inputAlphabet) := by
  have hb : (NativeInput.sourceCfg (observed m trueSymbol) inputAlphabet
      (Compiler.cfg (observed m trueSymbol) (TP.liftCfg m trueSymbol c))).l.isSome = true := by
    cases hl : c.l <;> simp_all [NativeInput.sourceCfg,embedCfg,Compiler.cfg,TP.liftCfg]
  have he (q : m.core.Stmt) :
      TM2.stepAux (embedStmt (NativeInput.layout (observed m trueSymbol))
        (NativeInput.states (observed m trueSymbol)) Sum.inr none
        (Compiler.statement (observed m trueSymbol) (TP.statement m trueSymbol q)))
        (Block.clear (observed m trueSymbol) (TP.clear m c.var))
        ((NativeInput.layout (observed m trueSymbol)).lift (Code.tapes (observed m trueSymbol) c.stk)) =
      NativeInput.sourceCfg (observed m trueSymbol) inputAlphabet
        (Compiler.cfg (observed m trueSymbol) (TP.liftCfg m trueSymbol (TM2.stepAux q c.var c.stk))) := by
    change TM2.stepAux _ ((NativeInput.states (observed m trueSymbol)).put _) _ = _
    rw [BinaryCompose.embed_stepAux]
    have hcoded := Compiler.statement_stepAux (observed m trueSymbol)
      (TP.statement m trueSymbol q) (TP.clear m c.var) c.stk
    rw [show TM2.stepAux (TP.statement m trueSymbol q) (TP.clear m c.var) c.stk =
      TP.liftCfg m trueSymbol (TM2.stepAux q c.var c.stk) from TP.statement_stepAux m trueSymbol q c.var c.stk] at hcoded
    exact congrArg (embedCfg (NativeInput.layout (observed m trueSymbol))
      (NativeInput.states (observed m trueSymbol)) Sum.inr none) hcoded
  rw [entry,base_step_active m trueSymbol inputAlphabet token _ hb]
  cases hl : c.l with
  | none => simp [hl] at hc
  | some l =>
    cases token with
    | none => cases hs : m.split l <;>
        simp [BinaryMachine.step,NativeInput.sourceCfg,embedCfg,Compiler.cfg,TP.liftCfg,
          hl,hs,base,NativeFinish.old,NativeInput.machine,NativeInput.computer,
          NativeInput.program,entry,TP.machine,TP.computer,observed,TP.clear,Block.clear] <;>
        first
        | exact congrArg (NativeFinish.cfg m trueSymbol inputAlphabet)
            (by simpa [NativeInput.sourceCfg,embedCfg,Compiler.cfg,TP.liftCfg,
              NativeInput.states,TP.clear,Block.clear] using he (m.core.m l))
        | exact congrArg (NativeFinish.cfg m trueSymbol inputAlphabet)
            (by simpa [NativeInput.sourceCfg,embedCfg,Compiler.cfg,TP.liftCfg,
              NativeInput.states,TP.clear,Block.clear] using he (m.alternate l))
    | some bit => cases bit <;> cases hs : m.split l <;>
        simp [BinaryMachine.step,NativeInput.sourceCfg,embedCfg,Compiler.cfg,TP.liftCfg,
          hl,hs,base,NativeFinish.old,NativeInput.machine,NativeInput.computer,
          NativeInput.program,entry,TP.machine,TP.computer,observed,TP.clear,Block.clear] <;>
        first
        | exact congrArg (NativeFinish.cfg m trueSymbol inputAlphabet)
            (by simpa [NativeInput.sourceCfg,embedCfg,Compiler.cfg,TP.liftCfg,
              NativeInput.states,TP.clear,Block.clear] using he (m.core.m l))
        | exact congrArg (NativeFinish.cfg m trueSymbol inputAlphabet)
            (by simpa [NativeInput.sourceCfg,embedCfg,Compiler.cfg,TP.liftCfg,
              NativeInput.states,TP.clear,Block.clear] using he (m.alternate l))

theorem source_advance_active (log : List Bool) (c : m.Config) (hc : c.l.isSome = true) :
    (native m trueSymbol inputAlphabet).advance (log,entry m trueSymbol inputAlphabet c) =
      (m.advance (log,c)).map (fun s => (s.1,entry m trueSymbol inputAlphabet s.2)) := by
  cases hl : c.l with
  | none => simp [hl] at hc
  | some l =>
    have he : (entry m trueSymbol inputAlphabet c).l = some (.inr l) := by
      simp [entry,NativeFinish.cfg,HS.restateCfg,NativeInput.sourceCfg,embedCfg,
        Compiler.cfg,TP.liftCfg,hl,NativeFinish.label]
    have hsplit : (native m trueSymbol inputAlphabet).split (.inr l) = m.split l := rfl
    cases hs : m.split l with
    | false =>
      simp only [BinaryMachine.advance,he,hl,hsplit,hs,Bool.false_eq_true,ite_false]
      rw [source_step_active m trueSymbol inputAlphabet none c hc]
      simp only [Option.map_map,Function.comp_def]
    | true => cases log with
      | nil => simp only [BinaryMachine.advance,he,hl,hsplit,hs,ite_true,Option.map_none]
      | cons bit rest =>
        simp only [BinaryMachine.advance,he,hl,hsplit,hs,ite_true]
        rw [source_step_active m trueSymbol inputAlphabet (some bit) c hc]
        simp only [Option.map_map,Function.comp_def]

/-- This name denotes the result of the existing literal decoder solely in a
proof. It is never loaded into the running machine or passed to its constructor. -/
def decoded (c : m.Config) : (native m trueSymbol inputAlphabet).Config :=
  TM2.stepAux (NativeFinish.program m trueSymbol inputAlphabet false (NativeFinish.decoderLabel m))
    (entry m trueSymbol inputAlphabet c).var (entry m trueSymbol inputAlphabet c).stk

theorem decoded_semantics (c : m.Config) :
    decoded m trueSymbol inputAlphabet c =
      embedCfg (NativeInput.layout (observed m trueSymbol)) (NativeInput.states (observed m trueSymbol))
        Sum.inr none
        (TM2.stepAux (Output.decoder m trueSymbol)
          (Block.clear (observed m trueSymbol) (TP.liftCfg m trueSymbol c).var)
          (Code.tapes (observed m trueSymbol) c.stk)) := by
  have hl : NativeFinish.oldLabel m trueSymbol (NativeFinish.decoderLabel m) = none := by
    simp [NativeFinish.oldLabel,NativeFinish.decoderLabel]
  simp only [decoded,NativeFinish.program,hl,Option.elim_none]
  exact BinaryCompose.embed_stepAux _ _ _ _ _ _ _

theorem decoded_halt (c : m.Config) : (decoded m trueSymbol inputAlphabet c).l = none := by
  rw [decoded_semantics]
  simp only [Output.decoder,Block.read_word]
  cases hh : (c.stk m.core.k₁).head? <;>
    simp [embedCfg,Output.emit,TM2.stepAux,hh,Block.clear,Block.setBit]

/-- A false old observer flag really emits a false head, whatever source
output/rest tapes were present. No decoder-success hypothesis is introduced. -/
theorem decoded_rejects_flag (c : m.Config)
    (hv : TP.acceptControl m (TP.liftCfg m trueSymbol c).var = false) :
    ((decoded m trueSymbol inputAlphabet c).stk
      (native m trueSymbol inputAlphabet).core.k₁).head? = some false := by
  rw [decoded_semantics]
  simp only [Output.decoder,Block.read_word]
  cases hh : (c.stk m.core.k₁).head? <;>
    simp [embedCfg,NativeInput.layout,NativeInput.tapes,NativeInput.source,
      NativeInput.states,NativeFinish.machine,NativeFinish.computer,Output.emit,
      TM2.stepAux,Block.clear,Block.setBit,hh,hv,observed]

theorem entry_true : entry m trueSymbol inputAlphabet (haltList m.core [trueSymbol]) =
    NativeFinish.decoderEntry m trueSymbol inputAlphabet := by
  rfl

theorem decoded_true_iff (c : m.Config) (hc : c.l = none) :
    decoded m trueSymbol inputAlphabet c = haltList (native m trueSymbol inputAlphabet).core [true] ↔
      c = haltList m.core [trueSymbol] := by
  constructor
  · intro hd
    have hv : TP.acceptControl m (TP.liftCfg m trueSymbol c).var = true := by
      cases hflag : TP.acceptControl m (TP.liftCfg m trueSymbol c).var with
      | true => rfl
      | false =>
        have hb := decoded_rejects_flag m trueSymbol inputAlphabet c hflag
        rw [hd] at hb
        simp [haltList] at hb
    exact (TP.endpoint_accepts_iff m trueSymbol c).mp ⟨hc,hv⟩
  · intro hd
    subst c
    have hs := NativeFinish.decoder_step m trueSymbol inputAlphabet
    change some (decoded m trueSymbol inputAlphabet (haltList m.core [trueSymbol])) =
      some (haltList (native m trueSymbol inputAlphabet).core [true]) at hs
    exact Option.some.inj hs

theorem decoder_advance (log : List Bool) (c : m.Config) (hc : c.l = none) :
    (native m trueSymbol inputAlphabet).advance (log,entry m trueSymbol inputAlphabet c) =
      some (log,decoded m trueSymbol inputAlphabet c) := by
  simp [BinaryMachine.advance,BinaryMachine.step,entry,NativeFinish.cfg,HS.restateCfg,
    NativeInput.sourceCfg,embedCfg,Compiler.cfg,TP.liftCfg,hc,NativeFinish.machine,
    NativeFinish.decoderLabel,NativeFinish.computer,decoded]

/-- Coupled phase invariant. A source halt gets exactly one deterministic
decoder edge; any later None edges hold its actual terminal. An active source
after n edges still takes its actual next instruction, never a free verdict. -/
theorem run_after (n : ℕ) (log : List Bool) (c : m.Config) :
    (native m trueSymbol inputAlphabet).run (n+1) (log,entry m trueSymbol inputAlphabet c) =
      (m.run n (log,c)).bind (fun s =>
        if s.2.l.isNone then some (s.1,decoded m trueSymbol inputAlphabet s.2)
        else (native m trueSymbol inputAlphabet).advance (s.1,entry m trueSymbol inputAlphabet s.2)) := by
  induction n generalizing log c with
  | zero =>
    rw [BinaryMachine.run_one]
    cases hl : c.l with
    | none => simpa [BinaryMachine.run,hl] using decoder_advance m trueSymbol inputAlphabet log c hl
    | some l => simp [BinaryMachine.run,hl]
  | succ n ih =>
    cases hl : c.l with
    | none =>
      rw [BinaryMachine.run,decoder_advance m trueSymbol inputAlphabet log c hl,Option.bind_some]
      rw [BinaryMachine.run_halt _ _ _ _ (decoded_halt m trueSymbol inputAlphabet c),
        BinaryMachine.run_halt _ _ _ _ hl]
      simp [hl]
    | some l =>
      have ha : c.l.isSome = true := by simp [hl]
      rw [BinaryMachine.run,source_advance_active m trueSymbol inputAlphabet log c ha]
      cases hs : m.advance (log,c) with
      | none => simp [hs,BinaryMachine.run]
      | some next =>
        simp only [hs,Option.map_some,Option.bind_some]
        rw [ih,BinaryMachine.run,hs,Option.bind_some]

theorem source_accepts_iff (n : ℕ) (log rest : List Bool) (c : m.Config) :
    (native m trueSymbol inputAlphabet).run (n+1) (log,entry m trueSymbol inputAlphabet c) =
      some (rest,haltList (native m trueSymbol inputAlphabet).core [true]) ↔
        m.run n (log,c) = some (rest,haltList m.core [trueSymbol]) := by
  rw [run_after]
  cases hr : m.run n (log,c) with
  | none => simp
  | some s =>
    rcases s with ⟨remaining,d⟩
    simp only [Option.bind_some]
    cases hl : d.l with
    | none =>
      simp only [hl,Option.isNone_none,ite_true,Option.some.injEq,Prod.mk.injEq]
      rw [decoded_true_iff m trueSymbol inputAlphabet d hl]
    | some l =>
      have ha : d.l.isSome = true := by simp [hl]
      simp only [hl,Option.isNone_some,Bool.false_eq_true,ite_false]
      rw [source_advance_active m trueSymbol inputAlphabet remaining d ha]
      cases hs : m.advance (remaining,d) with
      | none =>
        simp only [Option.map_none,reduceCtorEq,false_iff,Option.some.injEq,Prod.mk.injEq]
        rintro ⟨_,hd⟩
        have he := congrArg (fun q : m.Config => q.l) hd
        simpa [hl,haltList] using he
      | some next =>
        have hn := entry_active m trueSymbol inputAlphabet next.2
        constructor
        · intro h
          have he := congrArg (fun q : List Bool × (native m trueSymbol inputAlphabet).Config => q.2.l.isSome)
            (Option.some.inj (by simpa only [Option.map_some] using h))
          simp [hn,haltList] at he
        · intro h
          have he := congrArg (fun q : List Bool × m.Config => q.2.l) (Option.some.inj h)
          simp [hl,haltList] at he

/-- Trace append and unique held-halt padding, both derived from real steps. -/
theorem trace_append (b : BinaryMachine) (xs ys : List (Option Bool)) (c d : b.Config) :
    b.TraceValid (xs++ys) c d ↔ ∃ middle, b.TraceValid xs c middle ∧ b.TraceValid ys middle d := by
  induction xs generalizing c with
  | nil => simp [BinaryMachine.TraceValid]
  | cons token xs ih =>
    simp only [List.cons_append,BinaryMachine.TraceValid,ih]
    constructor
    · rintro ⟨next,hs,middle,hx,hy⟩; exact ⟨middle,⟨next,hs,hx⟩,hy⟩
    · rintro ⟨middle,⟨next,hs,hx⟩,hy⟩; exact ⟨next,hs,middle,hx,hy⟩

theorem trace_halt_iff (b : BinaryMachine) (xs : List (Option Bool)) (c d : b.Config) (hc : c.l = none) :
    b.TraceValid xs c d ↔ c = d ∧ xs = List.replicate xs.length none := by
  induction xs with
  | nil => simp [BinaryMachine.TraceValid]
  | cons token xs ih =>
    cases token with
    | some bit => simp [BinaryMachine.TraceValid,BinaryMachine.step,hc,List.replicate_succ]
    | none => simpa [BinaryMachine.TraceValid,BinaryMachine.step,hc,List.replicate_succ] using ih

theorem trace_hold (b : BinaryMachine) (n : ℕ) (c : b.Config) (hc : c.l = none) :
    b.TraceValid (List.replicate n none) c c :=
  (trace_halt_iff b _ c c hc).mpr ⟨rfl,by simp⟩

theorem replicate_none_snoc (n : ℕ) :
    List.replicate n (none : Option Bool)++[none] = none::List.replicate n none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

/-- Early source halt consumes the first old None padding edge as decoder;
all remaining old padding, plus the final added None, remains unique. -/
theorem source_trace (xs : List (Option Bool)) (c : m.Config)
    (h : m.TraceValid xs c (haltList m.core [trueSymbol])) :
    (native m trueSymbol inputAlphabet).TraceValid (xs++[none])
      (entry m trueSymbol inputAlphabet c) (haltList (native m trueSymbol inputAlphabet).core [true]) := by
  induction xs generalizing c with
  | nil =>
    change c = haltList m.core [trueSymbol] at h
    subst c
    refine ⟨haltList (native m trueSymbol inputAlphabet).core [true],?_,rfl⟩
    simpa [BinaryMachine.step,entry_true,NativeFinish.decoderEntry,NativeFinish.machine,
      NativeFinish.computer,NativeFinish.decoderLabel,FinTM2.step,TM2.step] using NativeFinish.decoder_step m trueSymbol inputAlphabet
  | cons token xs ih =>
    cases hl : c.l with
    | none =>
      obtain ⟨hc,hx⟩ := (trace_halt_iff m (token::xs) c _ hl).mp h
      subst c
      rw [hx]
      have he : List.replicate (token::xs).length none++[none] =
          none::List.replicate (token::xs).length none := replicate_none_snoc _
      rw [he]
      refine ⟨haltList (native m trueSymbol inputAlphabet).core [true],?_,trace_hold _ _ _ rfl⟩
      simpa [BinaryMachine.step,entry_true,NativeFinish.decoderEntry,NativeFinish.machine,
        NativeFinish.computer,NativeFinish.decoderLabel,FinTM2.step,TM2.step] using NativeFinish.decoder_step m trueSymbol inputAlphabet
    | some l =>
      obtain ⟨next,hs,ht⟩ := h
      refine ⟨entry m trueSymbol inputAlphabet next,?_,ih next ht⟩
      rw [source_step_active m trueSymbol inputAlphabet token c (by simp [hl]),hs]
      rfl

theorem filterMap_empty (xs : List (Option Bool)) (h : xs.filterMap id = []) :
    xs = List.replicate xs.length none := by
  induction xs with
  | nil => rfl
  | cons token xs ih =>
    cases token with
    | some bit => simp at h
    | none => have hz : xs.filterMap id = [] := by simpa using h
              simpa [List.replicate_succ] using congrArg (none::·) (ih hz)

theorem prepare_trace (word : List Bool) :
    (native m trueSymbol inputAlphabet).TraceValid
      (List.replicate (NativeInput.steps (observed m trueSymbol) word.length) none)
      (initList (native m trueSymbol inputAlphabet).core word)
      (entry m trueSymbol inputAlphabet (initList m.core (word.map inputAlphabet.symm))) := by
  obtain ⟨xs,hlen,hlog,ht⟩ := (native m trueSymbol inputAlphabet).run_trace _ _ _
    (prepare_run m trueSymbol inputAlphabet word [])
  have hz : xs.filterMap id = [] := by simpa only [List.append_nil] using hlog
  rw [filterMap_empty xs hz,hlen] at ht
  exact ht

section PrimitivePrefixes
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Proof of a literal opcode prefix, including its actual operation count.
This is not a second executor: tests and tape updates are exactly those of
TM2.stepAux, and costs are compared with the existing HeterogeneousCost.budget.
The earlier Staging relation has a different fixed state/alphabet type and
cannot be instantiated for NativeFinish's all-Bool programme. -/
inductive PrimitivePrefix : TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) →
    ℕ → σ → (∀ k, List (Γ k)) → Prop
  | here q v S : PrimitivePrefix q v S 0 v S
  | push k f q v S n u U :
      PrimitivePrefix q v (Function.update S k (f v::S k)) n u U →
        PrimitivePrefix (.push k f q) v S (n+1) u U
  | pop k f q v S n u U :
      PrimitivePrefix q (f v (S k).head?) (Function.update S k (S k).tail) n u U →
        PrimitivePrefix (.pop k f q) v S (n+1) u U
  | peek k f q v S n u U : PrimitivePrefix q (f v (S k).head?) S n u U →
      PrimitivePrefix (.peek k f q) v S (n+1) u U
  | load f q v S n u U : PrimitivePrefix q (f v) S n u U →
      PrimitivePrefix (.load f q) v S (n+1) u U
  | branch_true f q r v S n u U : f v = true → PrimitivePrefix q v S n u U →
      PrimitivePrefix (.branch f q r) v S (n+1) u U
  | branch_false f q r v S n u U : f v = false → PrimitivePrefix r v S n u U →
      PrimitivePrefix (.branch f q r) v S (n+1) u U
  | goto f v S : PrimitivePrefix (.goto f) v S 1 v S
  | halt v S : PrimitivePrefix .halt v S 1 v S

/-- The entire actual execute result has this derivation internally; an
execution/correctness witness is not required from a caller. -/
theorem primitive_full (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    PrimitivePrefix q v S (HeterogeneousCost.execute q v S).1
      (TM2.stepAux q v S).var (TM2.stepAux q v S).stk := by
  have hp : PrimitivePrefix q v S (HeterogeneousCost.execute q v S).1
      (HeterogeneousCost.execute q v S).2.var (HeterogeneousCost.execute q v S).2.stk := by
    induction q generalizing v S with
    | push k f q ih => exact PrimitivePrefix.push _ _ _ _ _ _ _ _ (ih _ _)
    | pop k f q ih => exact PrimitivePrefix.pop _ _ _ _ _ _ _ _ (ih _ _)
    | peek k f q ih => exact PrimitivePrefix.peek _ _ _ _ _ _ _ _ (ih _ _)
    | load f q ih => exact PrimitivePrefix.load _ _ _ _ _ _ _ (ih _ _)
    | branch f q r hq hr =>
      cases hf : f v with
      | false => simpa only [HeterogeneousCost.execute,hf,Bool.false_eq_true,ite_false] using
          PrimitivePrefix.branch_false f q r v S _ _ _ hf (hr v S)
      | true => simpa only [HeterogeneousCost.execute,hf,ite_true] using
          PrimitivePrefix.branch_true f q r v S _ _ _ hf (hq v S)
    | goto f => exact PrimitivePrefix.goto f v S
    | halt => exact PrimitivePrefix.halt v S
  simpa only [HeterogeneousCost.result] using hp

theorem primitive_prefix_cost (q : TM2.Stmt Γ Λ σ) (v u : σ)
    (S U : ∀ k, List (Γ k)) (n : ℕ) (h : PrimitivePrefix q v S n u U) :
    n ≤ HeterogeneousCost.budget q := by
  induction h with
  | here => exact Nat.zero_le _
  | push k f q v S n u U h ih => exact Nat.add_le_add_right ih 1
  | pop k f q v S n u U h ih => exact Nat.add_le_add_right ih 1
  | peek k f q v S n u U h ih => exact Nat.add_le_add_right ih 1
  | load f q v S n u U h ih => exact Nat.add_le_add_right ih 1
  | branch_true f q r v S n u U hf h ih =>
      exact Nat.add_le_add_right (ih.trans (Nat.le_max_left _ _)) 1
  | branch_false f q r v S n u U hf h ih =>
      exact Nat.add_le_add_right (ih.trans (Nat.le_max_right _ _)) 1
  | goto => exact Nat.le_refl _
  | halt => exact Nat.le_refl _

theorem primitive_prefix_capacity (q : TM2.Stmt Γ Λ σ) (v u : σ)
    (S U : ∀ k, List (Γ k)) (n : ℕ) (h : PrimitivePrefix q v S n u U)
    (B : ℕ) (hs : ∀ k, (S k).length ≤ B) : ∀ k, (U k).length ≤ B+n := by
  induction h generalizing B with
  | here => simpa using hs
  | push k f q v S n u U h ih =>
      have hu : ∀ j, ((Function.update S k (f v::S k)) j).length ≤ B+1 := by
        intro j
        by_cases hj : j = k
        · subst j; simpa using Nat.add_le_add_right (hs k) 1
        · simpa [hj] using (hs j).trans (Nat.le_add_right B 1)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (B+1) hu
  | pop k f q v S n u U h ih =>
      have hu : ∀ j, ((Function.update S k (S k).tail) j).length ≤ B := by
        intro j
        by_cases hj : j = k
        · subst j
          have ht : (S k).tail.length ≤ (S k).length := by simp
          simpa using ht.trans (hs k)
        · simpa [hj] using hs j
      intro j
      exact (ih B hu j).trans (Nat.add_le_add_left (Nat.le_add_right n 1) B)
  | peek k f q v S n u U h ih =>
      exact fun j => (ih B hs j).trans (Nat.add_le_add_left (Nat.le_add_right n 1) B)
  | load f q v S n u U h ih =>
      exact fun j => (ih B hs j).trans (Nat.add_le_add_left (Nat.le_add_right n 1) B)
  | branch_true f q r v S n u U hf h ih =>
      exact fun j => (ih B hs j).trans (Nat.add_le_add_left (Nat.le_add_right n 1) B)
  | branch_false f q r v S n u U hf h ih =>
      exact fun j => (ih B hs j).trans (Nat.add_le_add_left (Nat.le_add_right n 1) B)
  | goto => exact fun j => (hs j).trans (Nat.le_add_right B 1)
  | halt => exact fun j => (hs j).trans (Nat.le_add_right B 1)
end PrimitivePrefixes

section Witness
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)
abbrev original := Reverse.TapeAcceptance.Forward.original w
abbrev symbol := Reverse.TapeAcceptance.Forward.trueSymbol w
abbrev witnessMachine := native (original w) (symbol w) (Equiv.refl Bool)
def timePolynomial : Polynomial ℕ :=
  Polynomial.C (Code.width (Reverse.TapeAcceptance.Forward.observed w) (original w).core.k₀+1)*Polynomial.X+
    Polynomial.C 2+Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.timePolynomial w+Polynomial.C 1
def time (a : α) : ℕ := (timePolynomial w).eval (ea.encode a).length
theorem time_eq (a : α) : time w a =
    NativeInput.steps (Reverse.TapeAcceptance.Forward.observed w) (ea.encode a).length+
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a+1) := by
  simp [time,timePolynomial,NativeInput.steps,Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time,Nat.add_assoc]

/-- Complete raw-input, fixed-clock acceptance equivalence. -/
theorem accepts_iff (a : α) (log : List Bool) :
    (witnessMachine w).run (time w a)
      (log,initList (witnessMachine w).core (ea.encode a)) =
        some ([],haltList (witnessMachine w).core [true]) ↔
          Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.Accepts w a log := by
  rw [time_eq,Nat.add_comm
    (NativeInput.steps (Reverse.TapeAcceptance.Forward.observed w) (ea.encode a).length)
    (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a+1),BinaryMachine.run_add,prepare_run,Option.bind_some]
  simp only [Equiv.refl_symm,Equiv.coe_refl,List.map_id]
  rw [source_accepts_iff]
  simp only [Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.Accepts,WitnessMachine.terminal_eq_halt,
    symbol,Reverse.TapeAcceptance.Forward.trueSymbol,Equiv.coe_refl,List.map_id]

abbrev AcceptedLog (a : α) := {log : List Bool // (witnessMachine w).run (time w a)
  (log,initList (witnessMachine w).core (ea.encode a)) = some ([],haltList (witnessMachine w).core [true])}
def logEquiv (a : α) : AcceptedLog w a ≃ Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedPath w a where
  toFun p := ⟨p.val,(accepts_iff w a p.val).mp p.property⟩
  invFun p := ⟨p.val,(accepts_iff w a p.val).mpr p.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
abbrev PhysicalPath (a : α) := {xs : List (Option Bool) // xs.length = time w a ∧
  (witnessMachine w).TraceValid xs (initList (witnessMachine w).core (ea.encode a))
    (haltList (witnessMachine w).core [true])}

def fullTokens (a : α) (xs : List (Option Bool)) : List (Option Bool) :=
  List.replicate (NativeInput.steps (Reverse.TapeAcceptance.Forward.observed w) (ea.encode a).length) none++
    xs++[none]
theorem fullTokens_log (a : α) (xs : List (Option Bool)) :
    (fullTokens w a xs).filterMap id = xs.filterMap id := by
  simp [fullTokens]

def physicalForward (a : α) (p : Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.PhysicalPath w a) : PhysicalPath w a :=
  ⟨fullTokens w a p.val,by simp [fullTokens,time_eq,p.property.1,Nat.add_assoc],by
    simp only [fullTokens,List.append_assoc]
    apply (trace_append _ _ _ _ _).mpr
    refine ⟨entry (original w) (symbol w) (Equiv.refl Bool) (initList (original w).core (ea.encode a)),?_,?_⟩
    · simpa only [Equiv.refl_symm,Equiv.coe_refl,List.map_id] using prepare_trace (original w) (symbol w) (Equiv.refl Bool) (ea.encode a)
    · apply source_trace
      simpa only [symbol,Reverse.TapeAcceptance.Forward.trueSymbol,WitnessMachine.terminal_eq_halt] using p.property.2⟩

def originalLog (a : α) (p : PhysicalPath w a) : Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedPath w a :=
  (logEquiv w a) ⟨p.val.filterMap id,by
    have hr := ((witnessMachine w).reify_trace p.val _ _ p.property.2).1
    rw [p.property.1] at hr
    exact hr⟩

def physicalEquiv (a : α) : Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.PhysicalPath w a ≃ PhysicalPath w a where
  toFun := physicalForward w a
  invFun p := (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.physicalPathEquiv w a) (originalLog w a p)
  left_inv p := by
    apply Subtype.ext
    have h₁ := ((original w).reify_trace p.val _ _ p.property.2).2
    let q := (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.physicalPathEquiv w a)
      (originalLog w a (physicalForward w a p))
    have h₂ := ((original w).reify_trace q.val _ _ q.property.2).2
    have hlog : q.val.filterMap id = p.val.filterMap id := by
      exact (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.physicalTokens_spec w a _).2.1.trans
        (fullTokens_log w a p.val)
    rw [q.property.1,hlog] at h₂
    rw [p.property.1] at h₁
    exact h₂.symm.trans h₁
  right_inv p := by
    apply Subtype.ext
    let q := (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.physicalPathEquiv w a) (originalLog w a p)
    have hf := (physicalForward w a q).property
    have h₁ := ((witnessMachine w).reify_trace (physicalForward w a q).val _ _ hf.2).2
    have h₂ := ((witnessMachine w).reify_trace p.val _ _ p.property.2).2
    have hlog : (physicalForward w a q).val.filterMap id = p.val.filterMap id := by
      change (fullTokens w a q.val).filterMap id = _
      rw [fullTokens_log]
      exact (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.physicalTokens_spec w a _).2.1
    rw [hf.1,hlog] at h₁
    rw [p.property.1] at h₂
    exact h₁.symm.trans h₂

def acceptedEquiv (a : α) : Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness w a ≃ PhysicalPath w a :=
  (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.acceptedWitnessPhysicalEquiv w a).trans (physicalEquiv w a)
noncomputable instance physicalFintype (a : α) : Fintype (PhysicalPath w a) :=
  Fintype.ofEquiv (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness w a) (acceptedEquiv w a)
theorem physical_count (a : α) : Fintype.card (PhysicalPath w a) = f a := by
  rw [Fintype.card_congr (acceptedEquiv w a).symm,Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.accepted_witness_card]
  exact (w.counts a).symm
theorem choices_exact (a : α) (p : PhysicalPath w a) :
    (p.val.filterMap id).length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a ∧
      w.accept (a,(p.val.filterMap id).reverse) = true :=
  (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.accepts_iff w a _).mp (originalLog w a p).property
theorem tokens_preserved (a : α) (p : Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.PhysicalPath w a) :
    (physicalEquiv w a p).val = fullTokens w a p.val := rfl

def capacityPolynomial : Polynomial ℕ := Polynomial.X+timePolynomial w*Polynomial.C (witnessMachine w).pushBudget
def primitivePolynomial : Polynomial ℕ := timePolynomial w*Polynomial.C (witnessMachine w).primitiveBudget
def bitsPolynomial : Polynomial ℕ := Polynomial.C (witnessMachine w).controlBits+
  capacityPolynomial w*Polynomial.C (witnessMachine w).symbolWidths
def internalCapacityPolynomial : Polynomial ℕ := capacityPolynomial w+Polynomial.C (witnessMachine w).primitiveBudget
def internalBitsPolynomial : Polynomial ℕ := Polynomial.C (witnessMachine w).controlBits+
  internalCapacityPolynomial w*Polynomial.C (witnessMachine w).symbolWidths

theorem prefix_run (a : α) (p : PhysicalPath w a) (j : ℕ) (hj : j ≤ time w a) :
    ∃ next, (witnessMachine w).run j
      (p.val.filterMap id,initList (witnessMachine w).core (ea.encode a)) = some next := by
  have hr := ((witnessMachine w).reify_trace p.val _ _ p.property.2).1
  rw [p.property.1] at hr
  exact (witnessMachine w).prefix_exists _ _ _ _ hr hj
theorem prefix_capacity (a : α) (log : List Bool) (j : ℕ)
    (next : List Bool × (witnessMachine w).Config) (hj : j ≤ time w a)
    (hr : (witnessMachine w).run j (log,initList (witnessMachine w).core (ea.encode a)) = some next) :
    ∀ k, (next.2.stk k).length ≤ (capacityPolynomial w).eval (ea.encode a).length := by
  have hi : ∀ k, ((initList (witnessMachine w).core (ea.encode a)).stk k).length ≤ (ea.encode a).length := by
    intro k
    by_cases hk : k = (witnessMachine w).core.k₀ <;> simp [initList,hk]
  have hs := (witnessMachine w).run_stack_bound j _ _ (ea.encode a).length hi hr
  intro k
  exact (hs k).trans (by
    simpa [capacityPolynomial,time] using Nat.add_le_add_left
      (Nat.mul_le_mul_right (witnessMachine w).pushBudget hj) (ea.encode a).length)
theorem prefix_primitive (a : α) (log : List Bool) (j : ℕ) (hj : j ≤ time w a) :
    (witnessMachine w).primitiveCost j (log,initList (witnessMachine w).core (ea.encode a)) ≤
      (primitivePolynomial w).eval (ea.encode a).length := by
  exact ((witnessMachine w).primitiveCost_le j _).trans (by
    simpa [primitivePolynomial,time] using Nat.mul_le_mul_right (witnessMachine w).primitiveBudget hj)
theorem prefix_bits (a : α) (log : List Bool) (j : ℕ)
    (next : List Bool × (witnessMachine w).Config) (hj : j ≤ time w a)
    (hr : (witnessMachine w).run j (log,initList (witnessMachine w).core (ea.encode a)) = some next) :
    (witnessMachine w).codedStorageBits next.2 ≤ (bitsPolynomial w).eval (ea.encode a).length := by
  apply ((witnessMachine w).codedStorageBits_le next.2).trans
  simpa [bitsPolynomial] using (witnessMachine w).storageBits_le next.2 _
    (prefix_capacity w a log j next hj hr)

/-- Every primitive prefix of either actual table at the current control,
including raw preparation and the output decoder, has this internal bound.
The programme/clock/budgets are all constructed from w. -/
theorem internal_prefix (a : α) (log : List Bool) (j : ℕ)
    (next : List Bool × (witnessMachine w).Config) (hj : j < time w a)
    (hr : (witnessMachine w).run j (log,initList (witnessMachine w).core (ea.encode a)) = some next)
    (l : (witnessMachine w).core.Λ) (hl : next.2.l = some l) (b : Bool)
    (n : ℕ) (u : (witnessMachine w).core.σ) (U : (witnessMachine w).core.K → List Bool)
    (h : PrimitivePrefix (NativeFinish.program (original w) (symbol w) (Equiv.refl Bool) b l)
      next.2.var next.2.stk n u U) (control : Option (witnessMachine w).core.Λ) :
    (witnessMachine w).primitiveCost j (log,initList (witnessMachine w).core (ea.encode a))+(n+1) ≤
      (primitivePolynomial w).eval (ea.encode a).length ∧
    (witnessMachine w).codedStorageBits ⟨control,u,U⟩ ≤
      (internalBitsPolynomial w).eval (ea.encode a).length := by
  have hb : n+1 ≤ (witnessMachine w).primitiveBudget := by
    have hc := primitive_prefix_cost _ _ _ _ _ _ h
    cases b with
    | false => exact (Nat.add_le_add_right hc 1).trans ((witnessMachine w).core_budget_le l)
    | true => exact (Nat.add_le_add_right hc 1).trans ((witnessMachine w).alternate_budget_le l)
  constructor
  · have hc := (witnessMachine w).primitiveCost_le j
      (log,initList (witnessMachine w).core (ea.encode a))
    have ht := Nat.mul_le_mul_right (witnessMachine w).primitiveBudget (Nat.succ_le_of_lt hj)
    have he := Nat.add_le_add hc hb
    simp only [Nat.succ_mul] at ht
    exact he.trans (by simpa [primitivePolynomial,time] using ht)
  · have hs := prefix_capacity w a log j next (Nat.le_of_lt hj) hr
    have hu := primitive_prefix_capacity _ _ _ _ _ _ h _ hs
    have hU : ∀ k, (U k).length ≤ (internalCapacityPolynomial w).eval (ea.encode a).length := by
      intro k
      exact (hu k).trans (by
        simpa [internalCapacityPolynomial] using Nat.add_le_add_left ((Nat.le_add_right n 1).trans hb)
          ((capacityPolynomial w).eval (ea.encode a).length))
    exact ((witnessMachine w).codedStorageBits_le _).trans (by
      simpa [internalBitsPolynomial] using (witnessMachine w).storageBits_le ⟨control,u,U⟩ _ hU)
end Witness
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.NativeExecution
