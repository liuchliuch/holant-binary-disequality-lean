import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.Output

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Installed all-Boolean native-input program: raw-byte
preparation, the same original split instruction tables compiled to Bool, and
a real deterministic output-decoding successor at every original halt leaf.
The full bounded accepted-path/clock bijection across that successor is still
an explicit consumer obligation; this file does not assume it to close counts.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.NativeFinish
open Turing Computability Holant.Complexity BinaryCompose
variable (m : BinaryMachine) (trueSymbol : m.core.Γ m.core.k₁)
    (inputAlphabet : m.core.Γ m.core.k₀ ≃ Bool)
abbrev observed := Output.observed m trueSymbol
abbrev old := NativeInput.machine (observed m trueSymbol) inputAlphabet
abbrev Stack := NativeInput.Stack (observed m trueSymbol)
abbrev State := Block.State (observed m trueSymbol)
abbrev Label := Fin 3 ⊕ m.core.Λ
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k

def label : NativeInput.Label (observed m trueSymbol) → Label m
  | .inl i => .inl ⟨i.val,by omega⟩
  | .inr l => .inr l
def decoderLabel : Label m := .inl 2
def oldLabel : Label m → Option (NativeInput.Label (observed m trueSymbol))
  | .inl i => if h : i.val < 2 then some (.inl ⟨i.val,h⟩) else none
  | .inr l => some (.inr l)
def states : StateEmbedding (State m trueSymbol) (State m trueSymbol) := ⟨id,id,fun _ => rfl⟩

def program (alternate : Bool) (l : Label m) :
    TM2.Stmt (fun _ : Stack m trueSymbol => Bool) (Label m) (State m trueSymbol) :=
  (oldLabel m trueSymbol l).elim
    (embedStmt (NativeInput.layout (observed m trueSymbol))
      (NativeInput.states (observed m trueSymbol)) Sum.inr none (Output.decoder m trueSymbol))
    (fun source => Reverse.Staging.HeterogeneousSum.restateStmt
      (fun _ : Stack m trueSymbol => Bool) (states m trueSymbol) (label m trueSymbol)
      (some (decoderLabel m)) (NativeInput.program (observed m trueSymbol) inputAlphabet alternate source))

abbrev computer : FinTM2 where
  K := Stack m trueSymbol
  k₀ := NativeInput.raw (observed m trueSymbol)
  k₁ := NativeInput.source (observed m trueSymbol) m.core.k₁
  Γ := fun _ => Bool
  Λ := Label m
  main := label m trueSymbol (old m trueSymbol inputAlphabet).core.main
  σ := State m trueSymbol
  initialState := (old m trueSymbol inputAlphabet).core.initialState
  m := program m trueSymbol inputAlphabet false
abbrev machine : BinaryMachine where
  core := computer m trueSymbol inputAlphabet
  alternate := program m trueSymbol inputAlphabet true
  split
    | .inl _ => false
    | .inr l => m.split l
  alphabets _ := inferInstance

theorem oldLabel_label (l : NativeInput.Label (observed m trueSymbol)) :
    oldLabel m trueSymbol (label m trueSymbol l) = some l := by
  cases l with
  | inl i => simp [oldLabel,label,i.isLt]
  | inr l => rfl

theorem program_at_label (b : Bool) (l : NativeInput.Label (observed m trueSymbol)) :
    program m trueSymbol inputAlphabet b (label m trueSymbol l) =
      Reverse.Staging.HeterogeneousSum.restateStmt (fun _ : Stack m trueSymbol => Bool)
        (states m trueSymbol) (label m trueSymbol) (some (decoderLabel m))
        (NativeInput.program (observed m trueSymbol) inputAlphabet b l) := by
  rw [program,oldLabel_label]
  rfl

def cfg (c : (old m trueSymbol inputAlphabet).Config) : (machine m trueSymbol inputAlphabet).Config :=
  Reverse.Staging.HeterogeneousSum.restateCfg (fun _ : Stack m trueSymbol => Bool)
    (states m trueSymbol) (label m trueSymbol) (some (decoderLabel m)) c

/-- Empty branch-log success ending at an active control is real ordinary
TM2 execution. It is used only on the internally produced preparation run. -/
theorem empty_run_to_active (b : BinaryMachine) (n : ℕ) (c d : b.Config)
    (h : b.run n ([],c) = some ([],d)) (hd : d.l.isSome = true) :
    (fun p => p.bind b.core.step)^[n] (some c) = some d := by
  induction n generalizing c with
  | zero =>
    have hc : c = d := congrArg Prod.snd (Option.some.inj h)
    subst c
    rfl
  | succ n ih =>
    cases hl : c.l with
    | none =>
      have hh := b.run_halt (n+1) [] c hl
      have hc : c = d := congrArg Prod.snd (Option.some.inj (hh.symm.trans h))
      subst d
      simp [hl] at hd
    | some l =>
      cases hs : b.split l with
      | true => simp [BinaryMachine.run,BinaryMachine.advance,hl,hs] at h
      | false =>
        let next := TM2.stepAux (b.core.m l) c.var c.stk
        have ha : b.advance ([],c) = some ([],next) := by
          simp [BinaryMachine.advance,BinaryMachine.step,hl,hs,next]
        have hn : b.run n ([],next) = some ([],d) := by
          simpa only [BinaryMachine.run,ha,Option.bind_some] using h
        have ht : b.core.step c = some next := by
          cases c
          simp_all [FinTM2.step,TM2.step,next]
        rw [Function.iterate_succ_apply,Option.bind_some,ht]
        exact ih next hn

/-- Installed raw input preparation, with the actual final source-main control.
No already-coded initial configuration is supplied to this entry. -/
theorem prepare (word : List Bool) :
    (fun p => p.bind (computer m trueSymbol inputAlphabet).step)^[
      NativeInput.steps (observed m trueSymbol) word.length]
      (some (initList (computer m trueSymbol inputAlphabet) word)) =
        some (cfg m trueSymbol inputAlphabet
          (NativeInput.sourceCfg (observed m trueSymbol) inputAlphabet
            (Compiler.cfg (observed m trueSymbol)
              (initList (observed m trueSymbol).core (word.map inputAlphabet.symm))))) := by
  have hr := NativeInput.prepare (observed m trueSymbol) inputAlphabet word []
  have ht := empty_run_to_active (old m trueSymbol inputAlphabet) _ _ _ hr rfl
  have hc := Reverse.Staging.HeterogeneousSum.restate_run
    (fun _ : Stack m trueSymbol => Bool) (states m trueSymbol) (label m trueSymbol)
    (some (decoderLabel m)) (old m trueSymbol inputAlphabet).core.m
    (computer m trueSymbol inputAlphabet).m (program_at_label m trueSymbol inputAlphabet false)
    _ _ _ ht
  convert hc using 1 <;> rfl

def decoderEntry : (machine m trueSymbol inputAlphabet).Config :=
  ⟨some (decoderLabel m),
    (Compiler.cfg (observed m trueSymbol)
      (Reverse.TapeAcceptance.Program.liftCfg m trueSymbol (haltList m.core [trueSymbol]))).var,
    (NativeInput.layout (observed m trueSymbol)).lift
      (Compiler.cfg (observed m trueSymbol)
        (Reverse.TapeAcceptance.Program.liftCfg m trueSymbol (haltList m.core [trueSymbol]))).stk⟩

/-- The physical successor decodes the genuine old true output and halts
with exactly one plain Bool true, original state reset and every stack empty.
Its entry is constructed from the proved old observer terminal, not a flag input.
-/
theorem decoder_step : (computer m trueSymbol inputAlphabet).step
    (decoderEntry m trueSymbol inputAlphabet) =
      some (haltList (computer m trueSymbol inputAlphabet) [true]) := by
  change some (TM2.stepAux (program m trueSymbol inputAlphabet false (decoderLabel m))
    (decoderEntry m trueSymbol inputAlphabet).var (decoderEntry m trueSymbol inputAlphabet).stk) = _
  have hl : oldLabel m trueSymbol (decoderLabel m) = none := by simp [oldLabel,decoderLabel]
  rw [program,hl,Option.elim_none]
  change some (TM2.stepAux _
    ((NativeInput.states (observed m trueSymbol)).put
      (Compiler.cfg (observed m trueSymbol)
        (Reverse.TapeAcceptance.Program.liftCfg m trueSymbol (haltList m.core [trueSymbol]))).var)
    ((NativeInput.layout (observed m trueSymbol)).lift
      (Compiler.cfg (observed m trueSymbol)
        (Reverse.TapeAcceptance.Program.liftCfg m trueSymbol (haltList m.core [trueSymbol]))).stk)) = _
  rw [BinaryCompose.embed_stepAux,Output.decoder_true]
  congr 1
  change (⟨_,_,_⟩ : (machine m trueSymbol inputAlphabet).Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k with
  | inl u => simp [embedCfg,NativeInput.layout,NativeInput.tapes,haltList,computer,NativeInput.source]
  | inr k => cases k with
    | inl u => simp [embedCfg,NativeInput.layout,NativeInput.tapes,haltList,computer,NativeInput.source]
    | inr k => by_cases hk : k = m.core.k₁ <;>
        simp [embedCfg,NativeInput.layout,NativeInput.tapes,haltList,computer,NativeInput.source,hk]

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.NativeFinish
