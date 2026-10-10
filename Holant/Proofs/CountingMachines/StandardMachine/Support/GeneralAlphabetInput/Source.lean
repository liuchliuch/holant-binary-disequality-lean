import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetInput.Semantics
import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetInput.Program

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Sole arbitrary finite-input frontend entry. The same
original Γ symbols and packet bytes are physically initialized for the existing
staging machine, with an internally generated fixed alphabet code. The original
Boolean-input SharpPWitness capstone is neither changed nor applied to a cast
input. Whole frontend/source/output counting and independent conventional #P
model identification are not inferred from this initial-memory theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput.Source
open Turing Computability Holant.Complexity
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode
variable (m : BinaryMachine) (T : Polynomial ℕ) (accept : m.core.σ → Bool)
abbrev frontend := Program.machine (s m T accept)
abbrev timePolynomial := Program.timePolynomial (s m T accept)
abbrev capacityPolynomial := Program.capacityPolynomial (s m T accept)
abbrev primitivePolynomial := Program.primitivePolynomial (s m T accept)
abbrev bitsPolynomial := Program.bitsPolynomial (s m T accept)
abbrev internalBitsPolynomial := Program.internalBitsPolynomial (s m T accept)

/-- No equivalence Γinput ≃ Bool, ready configuration, decoded word or
prepared-memory correctness is provided by a caller. -/
theorem initialize_step (word : List (InputSymbol m)) (packets log : List Bool) :
    (frontend m T accept).run
      (Program.steps (s m T accept) (word.length+packets.length))
      (log,initList (frontend m T accept).core (raw m T accept word packets)) =
        some (log,Program.readyCfg (s m T accept) (sourceInitial m T accept word packets)) := by
  simpa only [taggedWord_length m,raw,rawCode,sourceInitial] using
    Program.prepare (s m T accept) (taggedWord m word packets) log

theorem initialize_time (word : List (InputSymbol m)) (packets : List Bool) :
    Program.steps (s m T accept) (word.length+packets.length) ≤
      (timePolynomial m T accept).eval (raw m T accept word packets).length := by
  simpa only [taggedWord_length m,raw,rawCode,sourceInitial] using
    Program.steps_le_bits (s m T accept) (taggedWord m word packets)

/-- Intermediate actual scan row: the new length tape counts complete tagged
symbols M=N+R. Original Γ length N is still computed by the SAME old staging
scanner; packet symbols do not change that old clock argument. -/
theorem length_scan (word : List (InputSymbol m)) (packets log : List Bool) :
    (frontend m T accept).run (word.length+packets.length+1)
      (log,Program.scanCfg (s m T accept) (raw m T accept word packets) [] []) =
        some (log,Program.moveCfg (s m T accept) (raw m T accept word packets).reverse
          (List.replicate (word.length+packets.length) true) []) := by
  simpa only [taggedWord_length m,raw,rawCode,List.append_nil] using
    Program.scan_run (s m T accept) (taggedWord m word packets) [] [] log

theorem original_clock (word : List (InputSymbol m)) (packets : List Bool) :
    T.eval (originalPart m (taggedWord m word packets)).length = T.eval word.length :=
  clock_argument m T word packets

/-- The entered source consumes exactly its old physical token, including
the two split choices and the sole None halt padding edge. -/
theorem source_edge (token : Option Bool) (c : (Compiler.machine (s m T accept)).Config) :
    (frontend m T accept).step token (Program.readyCfg (s m T accept) c) =
      ((Compiler.machine (s m T accept)).step token c).map (Program.readyCfg (s m T accept)) :=
  Program.source_step (s m T accept) token c

/-- After physical preparation, an original Γ symbol executes the SAME
staging row and increments its original-input unary length, not M or |raw|. -/
theorem original_scan (a : InputSymbol m) (input : List (TaggedSymbol m))
    (original : List (InputSymbol m)) (packets : List Bool) (n : ℕ) :
    (frontend m T accept).core.step
      (Program.readyCfg (s m T accept) (Compiler.cfg (s m T accept)
        (Reverse.Staging.Program.scanCfg m T accept false (.inl a::input) original packets n))) =
      some (Program.readyCfg (s m T accept) (Compiler.cfg (s m T accept)
        (Reverse.Staging.Program.scanCfg m T accept false input (a::original) packets (n+1)))) :=
  Program.source_core_step (s m T accept) _ _
    (coded_scan_left m T accept a input original packets n)

/-- Packet bytes retain the original length n on the actual installed row. -/
theorem packet_scan (seen bit : Bool) (input : List (TaggedSymbol m))
    (original : List (InputSymbol m)) (packets : List Bool) (n : ℕ) :
    (frontend m T accept).core.step
      (Program.readyCfg (s m T accept) (Compiler.cfg (s m T accept)
        (Reverse.Staging.Program.scanCfg m T accept seen (.inr bit::input) original packets n))) =
      some (Program.readyCfg (s m T accept) (Compiler.cfg (s m T accept)
        (Reverse.Staging.Program.scanCfg m T accept true input original (bit::packets) n))) :=
  Program.source_core_step (s m T accept) _ _
    (coded_scan_right m T accept seen bit input original packets n)

theorem ready_source (word : List (InputSymbol m)) (packets : List Bool)
    (k : (s m T accept).core.K) :
    (Program.readyCfg (s m T accept) (sourceInitial m T accept word packets)).stk
      (Program.source (s m T accept) k) = (sourceInitial m T accept word packets).stk k := rfl
theorem ready_new_empty (word : List (InputSymbol m)) (packets : List Bool) :
    let c := Program.readyCfg (s m T accept) (sourceInitial m T accept word packets)
    c.stk (Program.raw (s m T accept)) = [] ∧
      c.stk (Program.buffer (s m T accept)) = [] ∧ c.stk (Program.counter (s m T accept)) = [] :=
  ⟨rfl,rfl,rfl⟩
theorem ready_state (word : List (InputSymbol m)) (packets : List Bool) :
    (Program.readyCfg (s m T accept) (sourceInitial m T accept word packets)).var =
      Block.clear (s m T accept) (Reverse.Staging.Program.initial m T) :=
  initial_state m T accept word packets

/-- The new physical memory projects to the previously delivered empty
NativeInput frame. This uses only its layout, never its Γinput≃Bool machine. -/
def oldKey : NativeInput.Stack (s m T accept) → Program.Stack (s m T accept)
  | .inl _ => Program.raw (s m T accept)
  | .inr (.inl _) => Program.buffer (s m T accept)
  | .inr (.inr k) => Program.source (s m T accept) k
theorem old_frame (word : List (InputSymbol m)) (packets : List Bool)
    (k : NativeInput.Stack (s m T accept)) :
    (Program.readyCfg (s m T accept) (sourceInitial m T accept word packets)).stk (oldKey m T accept k) =
      framedInitial m T accept word packets k := by
  cases k with
  | inl _ => rfl
  | inr k => cases k <;> rfl

/-- Every actual frontend prefix is internally produced from raw serialized
bytes and bounded by their physical bit length. No capacity/time law is input. -/
theorem actual_prefix (word : List (InputSymbol m)) (packets log : List Bool) (j : ℕ)
    (hj : j ≤ Program.steps (s m T accept) (word.length+packets.length)) :
    ∃ next : List Bool × (frontend m T accept).Config,
      (frontend m T accept).run j
        (log,initList (frontend m T accept).core (raw m T accept word packets)) = some next ∧
      (∀ k, (next.2.stk k).length ≤ (capacityPolynomial m T accept).eval (raw m T accept word packets).length) ∧
      (frontend m T accept).primitiveCost j
        (log,initList (frontend m T accept).core (raw m T accept word packets)) ≤
          (primitivePolynomial m T accept).eval (raw m T accept word packets).length ∧
      (frontend m T accept).codedStorageBits next.2 ≤
        (bitsPolynomial m T accept).eval (raw m T accept word packets).length := by
  obtain ⟨next,hr⟩ := (frontend m T accept).prefix_exists _ _ _ _
    (initialize_step m T accept word packets log) hj
  have ht := hj.trans (initialize_time m T accept word packets)
  exact ⟨next,hr,Program.prefix_capacity _ _ _ _ next ht hr,
    Program.prefix_primitive _ _ _ _ ht,Program.prefix_bits _ _ _ _ next ht hr⟩

/-- The frontend has no choices: all consumed preparation tokens are None;
this conclusion is recovered from actual log conservation, not assumed. -/
theorem canonical_trace (word : List (InputSymbol m)) (packets : List Bool) :
    (frontend m T accept).TraceValid
      (List.replicate (Program.steps (s m T accept) (word.length+packets.length)) none)
      (initList (frontend m T accept).core (raw m T accept word packets))
      (Program.readyCfg (s m T accept) (sourceInitial m T accept word packets)) := by
  obtain ⟨xs,hlen,hlog,ht⟩ := (frontend m T accept).run_trace _ _ _
    (initialize_step m T accept word packets [])
  have hz : xs.filterMap id = [] := by simpa only [List.append_nil] using hlog
  rw [NativeExecution.filterMap_empty xs hz,hlen] at ht
  exact ht

/-- Literal scanner/copy/clear/source opcode prefixes use the same physical
bit-length bound. The actual programme is never replaced by a cost interface. -/
theorem internal_prefix (input log : List Bool) (j : ℕ)
    (next : List Bool × (frontend m T accept).Config)
    (hj : j < (timePolynomial m T accept).eval input.length)
    (hr : (frontend m T accept).run j (log,initList (frontend m T accept).core input) = some next)
    (l : (frontend m T accept).core.Λ) (hl : next.2.l = some l) (alternate : Bool)
    (n : ℕ) (v : (frontend m T accept).core.σ) (S : (frontend m T accept).core.K → List Bool)
    (hp : NativeExecution.PrimitivePrefix (Program.program (s m T accept) alternate l)
      next.2.var next.2.stk n v S) (control : Option (frontend m T accept).core.Λ) :
    (frontend m T accept).primitiveCost j (log,initList (frontend m T accept).core input)+(n+1) ≤
      (primitivePolynomial m T accept).eval input.length ∧
    (frontend m T accept).codedStorageBits ⟨control,v,S⟩ ≤
      (internalBitsPolynomial m T accept).eval input.length :=
  Program.internal_prefix _ input log j next hj hr l hl alternate n v S hp control

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput.Source
