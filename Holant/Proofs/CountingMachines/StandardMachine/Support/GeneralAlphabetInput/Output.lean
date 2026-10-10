import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetInput.Source

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. A literal output successor for the SAME arbitrary-Γ
serialized staging frontend. The old staging cleaner produces the tagged
singleton verdict. This finite block reader consumes its code, checks EOF and
the old validity bit, emits one plain Bool, then resets the entire state.
No Γ≃Bool input equivalence or supplied decoder-success law is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput.Output
open Turing Computability Holant.Complexity BinaryCompose
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode
namespace HS
export Reverse.Staging.HeterogeneousSum (restateStmt restateCfg restate_stepAux restate_run)
end HS
variable (m : BinaryMachine) (T : Polynomial ℕ) (accept : m.core.σ → Bool)
abbrev staged := s m T accept
abbrev old := Program.machine (staged m T accept)
abbrev Stack := Program.Stack (staged m T accept)
abbrev Label := Option (Program.Label (staged m T accept))
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance : Fintype (Stack m T accept) := (old m T accept).core.kFin
local instance : Fintype (Program.Label (staged m T accept)) := (old m T accept).core.ΛFin
local instance : Fintype (staged m T accept).core.K := (staged m T accept).core.kFin
local instance : Fintype (staged m T accept).core.Λ := (staged m T accept).core.ΛFin
local instance : Fintype (staged m T accept).core.σ := (staged m T accept).core.σFin
local instance (k : (staged m T accept).core.K) : Fintype ((staged m T accept).core.Γ k) :=
  (staged m T accept).alphabets k
local instance : DecidableEq ((staged m T accept).core.Γ (staged m T accept).core.k₁) :=
  Classical.decEq _

def symbol (value : Bool) : (staged m T accept).core.Γ (staged m T accept).core.k₁ := Sum.inr value

/-- This finite metadata is not executed. Its extra original-control Bool
caches the source validity bit, so Block.clear cannot erase that observation. -/
def decoderMetadata : BinaryMachine where
  core := {
    K := (staged m T accept).core.K
    k₀ := (staged m T accept).core.k₀
    k₁ := (staged m T accept).core.k₁
    Γ := (staged m T accept).core.Γ
    Λ := (staged m T accept).core.Λ
    main := (staged m T accept).core.main
    σ := (staged m T accept).core.σ × Bool
    initialState := ((staged m T accept).core.initialState,true)
    m := fun _ => .halt }
  alternate := fun _ => .halt
  split _ := false
  alphabets := (staged m T accept).alphabets
@[simp] theorem decoder_width (k : (staged m T accept).core.K) :
    Code.width (decoderMetadata m T accept) k = Code.width (staged m T accept) k := rfl
@[simp] theorem decoder_word (k : (staged m T accept).core.K) (word : List ((staged m T accept).core.Γ k)) :
    Code.word (decoderMetadata m T accept) k word = Code.word (staged m T accept) k word := rfl
abbrev State := Block.State (decoderMetadata m T accept)
def states : StateEmbedding (Program.State (staged m T accept)) (State m T accept) where
  put v := ((v.1,v.2.2),v.2.1,v.2.2)
  get v := (v.1.1,v.2.1,v.2.2)
  get_put _ := rfl
def decoderStates : StateEmbedding (State m T accept) (State m T accept) := ⟨id,id,fun _ => rfl⟩

/-- The first load retains the actually produced validity bit. A source
candidate is accepted only if the real next output-tape peek observes EOF. -/
def emit (candidate : Bool) : TM2.Stmt (fun _ : (staged m T accept).core.K => Bool)
    (staged m T accept).core.Λ (State m T accept) :=
  .load (fun v => (v.1,none,(v.1.2 && v.2.2) && candidate))
    (.peek (staged m T accept).core.k₁ (Block.setBit (decoderMetadata m T accept))
      (.push (staged m T accept).core.k₁ (fun v => v.2.2 && v.2.1.isNone)
        (.load (fun _ => Block.clear (decoderMetadata m T accept)
          (decoderMetadata m T accept).core.initialState) .halt)))
def decoder : TM2.Stmt (fun _ : (staged m T accept).core.K => Bool)
    (staged m T accept).core.Λ (State m T accept) := by
  classical
  exact Block.readSymbol (decoderMetadata m T accept) (staged m T accept).core.k₁
    (fun head => head.elim (emit m T accept false)
      (fun a => emit m T accept (decide (a = symbol m T accept true))))

theorem emit_head (candidate : Bool) (v : State m T accept)
    (S : (staged m T accept).core.K → List Bool) :
    (TM2.stepAux (emit m T accept candidate) v S).stk (staged m T accept).core.k₁ =
      (((v.1.2 && v.2.2) && candidate) && (S (staged m T accept).core.k₁).head?.isNone)::
        S (staged m T accept).core.k₁ := by
  simp [emit,TM2.stepAux,Block.setBit]

/-- On any source-coded output, the actual reader preserves the cached old
validity bit. The actual next-tape peek, after exactly one complete symbol,
decides EOF; an extra coded output symbol makes the emitted head false. -/
theorem decoder_coded_head (v : Program.State (staged m T accept))
    (S : ∀ k, List ((staged m T accept).core.Γ k)) :
    (TM2.stepAux (decoder m T accept) ((states m T accept).put v)
      (Code.tapes (staged m T accept) S)).stk (staged m T accept).core.k₁ =
        ((v.2.2 && (S (staged m T accept).core.k₁).head?.elim false
          (fun a => decide (a = symbol m T accept true))) &&
            (Code.word (staged m T accept) (staged m T accept).core.k₁
              (S (staged m T accept).core.k₁).tail).head?.isNone)::
          Code.word (staged m T accept) (staged m T accept).core.k₁
            (S (staged m T accept).core.k₁).tail := by
  change (TM2.stepAux (decoder m T accept) ((states m T accept).put v)
    (Code.tapes (decoderMetadata m T accept) S)).stk _ = _
  rw [decoder,Block.read_word]
  cases hh : (S (staged m T accept).core.k₁).head? <;>
    simp [Option.elim,emit,TM2.stepAux,states,Block.clear,Block.setBit,Code.tapes,hh]

theorem decoder_budget : HeterogeneousCost.budget (decoder m T accept) ≤
    3*Code.width (staged m T accept) (staged m T accept).core.k₁+8 := by
  classical
  have hc : ∀ head : Option ((staged m T accept).core.Γ (staged m T accept).core.k₁), HeterogeneousCost.budget
      (head.elim (emit m T accept false)
        (fun a => emit m T accept (decide (a = symbol m T accept true)))) ≤ 5 := by
    intro head
    cases head <;> exact Nat.le_refl _
  convert Block.read_budget (decoderMetadata m T accept) (staged m T accept).core.k₁ _ 5 hc
      (Code.width (staged m T accept) (staged m T accept).core.k₁) [] using 1 <;> rfl

def boolTerminal (value : Bool) :
    TM2.Cfg (fun _ : (staged m T accept).core.K => Bool) (staged m T accept).core.Λ (State m T accept) :=
  ⟨none,Block.clear (decoderMetadata m T accept) (decoderMetadata m T accept).core.initialState,
    Function.update (fun _ => []) (staged m T accept).core.k₁ [value]⟩

/-- Both true and false are decoded from the actual old clean terminal, not
from an externally selected register value or a decoder-success premise. -/
theorem decoder_terminal (value : Bool) :
    TM2.stepAux (decoder m T accept)
      ((states m T accept).put ((Compiler.cfg (staged m T accept)
        (haltList (staged m T accept).core [symbol m T accept value])).var))
      (Compiler.cfg (staged m T accept)
        (haltList (staged m T accept).core [symbol m T accept value])).stk =
      boolTerminal m T accept value := by
  let S : (staged m T accept).core.K → List Bool := fun _ => []
  have hs : Code.tapes (staged m T accept)
      (haltList (staged m T accept).core [symbol m T accept value]).stk =
        Function.update S (staged m T accept).core.k₁
          (Code.symbol (decoderMetadata m T accept) (staged m T accept).core.k₁
            (symbol m T accept value)++S (staged m T accept).core.k₁) := by
    funext k
    by_cases hk : k = (staged m T accept).core.k₁
    · subst k
      simp [Code.tapes,Code.word,haltList,S]
      rfl
    · simp [Code.tapes,Code.word,haltList,S,hk]
  change TM2.stepAux (decoder m T accept)
    (Block.clear (decoderMetadata m T accept) (decoderMetadata m T accept).core.initialState)
    (Code.tapes (staged m T accept)
      (haltList (staged m T accept).core [symbol m T accept value]).stk) = _
  rw [hs,decoder,Block.read_symbol]
  have hd : decide (symbol m T accept value = symbol m T accept true) = value := by
    cases value with
    | false => apply decide_eq_false; intro h; have hh := Sum.inr.inj h; cases hh
    | true => exact decide_eq_true rfl
  simp only [Option.elim_some,hd]
  simp [emit,TM2.stepAux,Block.clear,Block.setBit,S,boolTerminal,decoderMetadata]

/-- All old labels retain their original actual statements. Only their halt
leaf is redirected to one new deterministic decoder label. -/
def program (alternate : Bool) : Label m T accept →
    TM2.Stmt (fun _ : Stack m T accept => Bool) (Label m T accept) (State m T accept)
  | none => embedStmt (Program.layout (staged m T accept)) (decoderStates m T accept)
      (fun l => some (Sum.inr l)) none (decoder m T accept)
  | some l => HS.restateStmt (fun _ : Stack m T accept => Bool) (states m T accept)
      some (some none) (Program.program (staged m T accept) alternate l)
abbrev computer : FinTM2 where
  K := Stack m T accept
  k₀ := (old m T accept).core.k₀
  k₁ := (old m T accept).core.k₁
  Γ := fun _ => Bool
  Λ := Label m T accept
  main := some (old m T accept).core.main
  σ := State m T accept
  initialState := (states m T accept).put (old m T accept).core.initialState
  m := program m T accept false
abbrev machine : BinaryMachine where
  core := computer m T accept
  alternate := program m T accept true
  split _ := false
  alphabets _ := inferInstance

theorem program_at_label (alternate : Bool) (l : Program.Label (staged m T accept)) :
    program m T accept alternate (some l) =
      HS.restateStmt (fun _ : Stack m T accept => Bool) (states m T accept)
        some (some none) (Program.program (staged m T accept) alternate l) := rfl
def cfg (c : (old m T accept).Config) : (machine m T accept).Config :=
  HS.restateCfg (fun _ : Stack m T accept => Bool) (states m T accept) some (some none) c
def entry (c : (staged m T accept).Config) : (machine m T accept).Config :=
  cfg m T accept (Program.readyCfg (staged m T accept) (Compiler.cfg (staged m T accept) c))

theorem decoder_step (value : Bool) :
    (computer m T accept).step
      (entry m T accept (haltList (staged m T accept).core [symbol m T accept value])) =
        some (haltList (computer m T accept) [value]) := by
  change some (TM2.stepAux (program m T accept false none)
    (entry m T accept (haltList (staged m T accept).core [symbol m T accept value])).var
    (entry m T accept (haltList (staged m T accept).core [symbol m T accept value])).stk) = _
  rw [program]
  change some (TM2.stepAux _ ((decoderStates m T accept).put
    ((states m T accept).put ((Compiler.cfg (staged m T accept)
      (haltList (staged m T accept).core [symbol m T accept value])).var)))
    ((Program.layout (staged m T accept)).lift
      (Compiler.cfg (staged m T accept)
        (haltList (staged m T accept).core [symbol m T accept value])).stk)) = _
  rw [embed_stepAux,decoder_terminal]
  congr 1
  change (⟨_,_,_⟩ : (machine m T accept).Config) = ⟨_,_,_⟩
  congr 1
  funext k
  cases k with
  | inl _ => simp [embedCfg,Program.layout,Program.tapes,haltList,computer,old,Program.machine,
      Program.computer,Program.source,boolTerminal,decoderStates,states,decoderMetadata,Block.clear]
  | inr k => cases k with
    | inl _ => simp [embedCfg,Program.layout,Program.tapes,haltList,computer,old,Program.machine,
        Program.computer,Program.source,boolTerminal,decoderStates,states,decoderMetadata,Block.clear]
    | inr k => cases k with
      | inl _ => simp [embedCfg,Program.layout,Program.tapes,haltList,computer,old,Program.machine,
          Program.computer,Program.source,boolTerminal,decoderStates,states,decoderMetadata,Block.clear]
      | inr k => by_cases hk : k = (staged m T accept).core.k₁ <;>
          simp [embedCfg,Program.layout,Program.tapes,haltList,computer,old,
            Program.machine,Program.computer,Program.source,boolTerminal,decoderStates,states,
            decoderMetadata,Block.clear,hk]

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput.Output
