import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetInput.Encoding
import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.NativeInput

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Whole literal coded initial memory for the SAME
heterogeneous staging machine. Original, packet and polynomial-clock work
tapes start empty; only its original tagged input tape carries encoded bytes.
The two scan equations consume the existing actual staging and opcode
instruction semantics. No prepared configuration is a hypothesis. This file
does not replace the old Boolean SharpPWitness capstone or claim a #P theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput
open Turing Computability Holant.Complexity
open scoped BigOperators

variable (m : BinaryMachine) (T : Polynomial ℕ) (accept : m.core.σ → Bool)
local instance : Fintype (s m T accept).core.K := (s m T accept).core.kFin

def sourceInitial (word : List (InputSymbol m)) (packets : List Bool) :
    (BooleanOpcode.Compiler.machine (s m T accept)).Config :=
  BooleanOpcode.Compiler.cfg (s m T accept)
    (initList (s m T accept).core (taggedWord m word packets))

/-- This is the actual single-stack init, not a supplied coded tape layout. -/
theorem initial_coded (word : List (InputSymbol m)) (packets : List Bool) :
    sourceInitial m T accept word packets =
      initList (BooleanOpcode.Compiler.computer (s m T accept)) (raw m T accept word packets) :=
  BooleanOpcode.Compiler.cfg_init (s m T accept) (taggedWord m word packets)

theorem initial_label (word : List (InputSymbol m)) (packets : List Bool) :
    (sourceInitial m T accept word packets).l =
      some (Reverse.Staging.Program.scanner m T 0) := rfl

theorem initial_state (word : List (InputSymbol m)) (packets : List Bool) :
    (sourceInitial m T accept word packets).var =
      BooleanOpcode.Block.clear (s m T accept) (Reverse.Staging.Program.initial m T) := rfl

theorem initial_tapes (word : List (InputSymbol m)) (packets : List Bool) :
    (sourceInitial m T accept word packets).stk =
      Function.update (fun _ : (s m T accept).core.K => [])
        (s m T accept).core.k₀ (raw m T accept word packets) := by
  rw [initial_coded]
  funext k
  by_cases hk : k = (s m T accept).core.k₀
  · subst k
    simp [initList,BooleanOpcode.Compiler.computer]
  · simp [initList,BooleanOpcode.Compiler.computer,hk]

theorem initial_raw (word : List (InputSymbol m)) (packets : List Bool) :
    (sourceInitial m T accept word packets).stk (Reverse.Staging.Program.raw m T) =
      raw m T accept word packets := by
  rw [initial_tapes]
  exact Function.update_self _ _ _

theorem initial_other_empty (word : List (InputSymbol m)) (packets : List Bool)
    (k : (s m T accept).core.K) (hk : k ≠ (s m T accept).core.k₀) :
    (sourceInitial m T accept word packets).stk k = [] := by
  rw [initial_tapes]
  simp only [Function.update_of_ne hk]

/-- All clock-machine tapes are empty even when the clock has a nonzero
constant term. Its own physical program subsequently computes T(|word|). -/
theorem initial_clock_empty (word : List (InputSymbol m)) (packets : List Bool)
    (k : (Reverse.Staging.Program.clock T).K) :
    (sourceInitial m T accept word packets).stk (Sum.inl k) = [] := by
  apply initial_other_empty
  simp [s,Reverse.Staging.Program.deterministic,Reverse.Staging.Program.computer,
    Reverse.Staging.Program.raw]

theorem initial_original_empty (word : List (InputSymbol m)) (packets : List Bool)
    (k : m.core.K) :
    (sourceInitial m T accept word packets).stk (Sum.inr (Sum.inr (Sum.inr k))) = [] := by
  apply initial_other_empty
  simp [s,Reverse.Staging.Program.deterministic,Reverse.Staging.Program.computer,
    Reverse.Staging.Program.raw]

theorem initial_packet_empty (word : List (InputSymbol m)) (packets : List Bool) :
    (sourceInitial m T accept word packets).stk (Reverse.Staging.Program.packet m T) = [] := by
  apply initial_other_empty
  simp [s,Reverse.Staging.Program.deterministic,Reverse.Staging.Program.computer,
    Reverse.Staging.Program.raw,Reverse.Staging.Program.packet]

theorem initial_storage (word : List (InputSymbol m)) (packets : List Bool) :
    (∑ k,((sourceInitial m T accept word packets).stk k).length) =
      rawWidth m T accept * (word.length+packets.length) := by
  classical
  rw [← raw_length]
  calc
    (∑ k,((sourceInitial m T accept word packets).stk k).length) =
        ((sourceInitial m T accept word packets).stk (s m T accept).core.k₀).length := by
      apply Finset.sum_eq_single
      · intro k _ hk
        rw [initial_other_empty m T accept word packets k hk]
        rfl
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    _ = (raw m T accept word packets).length := congrArg List.length (initial_raw m T accept word packets)

theorem initial_scan (word : List (InputSymbol m)) (packets : List Bool) :
    sourceInitial m T accept word packets = BooleanOpcode.Compiler.cfg (s m T accept)
      (Reverse.Staging.Program.scanCfg m T accept false (taggedWord m word packets) [] [] 0) :=
  congrArg (BooleanOpcode.Compiler.cfg (s m T accept))
    (Reverse.Staging.Program.initial_raw m T accept (taggedWord m word packets)).symm

/-- The clock argument is the ORIGINAL symbol count, rather than packet
length, tagged length or fixed-width Boolean serialization length. -/
theorem clock_argument (word : List (InputSymbol m)) (packets : List Bool) :
    T.eval (originalPart m (taggedWord m word packets)).length = T.eval word.length := by
  rw [originalPart_taggedWord]

/-- The existing empty-frame embedding is available without an input-alphabet
equivalence. This is a constructed memory view for the physical frontend. -/
def framedInitial (word : List (InputSymbol m)) (packets : List Bool) :
    BooleanOpcode.NativeInput.Stack (s m T accept) → List Bool :=
  (BooleanOpcode.NativeInput.layout (s m T accept)).lift
    (sourceInitial m T accept word packets).stk

theorem framed_source (word : List (InputSymbol m)) (packets : List Bool)
    (k : (s m T accept).core.K) :
    framedInitial m T accept word packets (BooleanOpcode.NativeInput.source (s m T accept) k) =
      (sourceInitial m T accept word packets).stk k := rfl
theorem framed_raw_empty (word : List (InputSymbol m)) (packets : List Bool) :
    framedInitial m T accept word packets (BooleanOpcode.NativeInput.raw (s m T accept)) = [] := rfl
theorem framed_buffer_empty (word : List (InputSymbol m)) (packets : List Bool) :
    framedInitial m T accept word packets (BooleanOpcode.NativeInput.buffer (s m T accept)) = [] := rfl

/-- A Γinput symbol advances the ORIGINAL unary length by exactly one in
the existing staging instruction. Code.bit/decode never execute as callbacks. -/
theorem coded_scan_left (a : InputSymbol m) (input : List (TaggedSymbol m))
    (original : List (InputSymbol m)) (packets : List Bool) (n : ℕ) :
    (BooleanOpcode.Compiler.computer (s m T accept)).step
      (BooleanOpcode.Compiler.cfg (s m T accept)
        (Reverse.Staging.Program.scanCfg m T accept false (.inl a::input) original packets n)) =
      some (BooleanOpcode.Compiler.cfg (s m T accept)
        (Reverse.Staging.Program.scanCfg m T accept false input (a::original) packets (n+1))) := by
  have hs := Reverse.Staging.Program.scan_left m T accept a input original packets n
  change some (TM2.stepAux ((s m T accept).core.m (Reverse.Staging.Program.scanner m T 0))
    (Reverse.Staging.Program.scanCfg m T accept false (.inl a::input) original packets n).var
    (Reverse.Staging.Program.scanCfg m T accept false (.inl a::input) original packets n).stk) = _ at hs
  change some (TM2.stepAux (BooleanOpcode.Compiler.statement (s m T accept)
    ((s m T accept).core.m (Reverse.Staging.Program.scanner m T 0)))
    (BooleanOpcode.Block.clear (s m T accept)
      (Reverse.Staging.Program.scanCfg m T accept false (.inl a::input) original packets n).var)
    (BooleanOpcode.Code.tapes (s m T accept)
      (Reverse.Staging.Program.scanCfg m T accept false (.inl a::input) original packets n).stk)) = _
  rw [BooleanOpcode.Compiler.statement_stepAux,Option.some.inj hs]

theorem coded_scan_right (seen : Bool) (b : Bool) (input : List (TaggedSymbol m))
    (original : List (InputSymbol m)) (packets : List Bool) (n : ℕ) :
    (BooleanOpcode.Compiler.computer (s m T accept)).step
      (BooleanOpcode.Compiler.cfg (s m T accept)
        (Reverse.Staging.Program.scanCfg m T accept seen (.inr b::input) original packets n)) =
      some (BooleanOpcode.Compiler.cfg (s m T accept)
        (Reverse.Staging.Program.scanCfg m T accept true input original (b::packets) n)) := by
  have hs := Reverse.Staging.Program.scan_right m T accept seen b input original packets n
  change some (TM2.stepAux ((s m T accept).core.m (Reverse.Staging.Program.scanner m T 0))
    (Reverse.Staging.Program.scanCfg m T accept seen (.inr b::input) original packets n).var
    (Reverse.Staging.Program.scanCfg m T accept seen (.inr b::input) original packets n).stk) = _ at hs
  change some (TM2.stepAux (BooleanOpcode.Compiler.statement (s m T accept)
    ((s m T accept).core.m (Reverse.Staging.Program.scanner m T 0)))
    (BooleanOpcode.Block.clear (s m T accept)
      (Reverse.Staging.Program.scanCfg m T accept seen (.inr b::input) original packets n).var)
    (BooleanOpcode.Code.tapes (s m T accept)
      (Reverse.Staging.Program.scanCfg m T accept seen (.inr b::input) original packets n).stk)) = _
  rw [BooleanOpcode.Compiler.statement_stepAux,Option.some.inj hs]

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput
