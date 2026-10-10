import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralAlphabetInput.Output

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Sole complete valid-tagged-input native entry. All
physical preparation, old staging execution, cleanup and Bool decoding come
from the installed finite programmes. The original polynomial clock is T(N),
while the whole native resource bound is evaluated at original serialized
bit length. Arbitrary malformed raw serialization and a conventional #P model
identification remain separate obligations; no such law is an input here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput.NativeExecution
open Turing Computability Holant.Complexity BinaryCompose
open Reverse
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode
namespace Stage
export Reverse.Staging.Program (outputs packetEval packet_accepts_iff timePolynomial)
end Stage
variable (m : BinaryMachine) (T : Polynomial ℕ) (accept : m.core.σ → Bool)
abbrev staged := s m T accept
abbrev native := Output.machine m T accept
abbrev verdict (word : List (InputSymbol m)) (packets : List Bool) :=
  Stage.packetEval m accept (T.eval word.length) packets (initList m.core word)
def timePolynomial : Polynomial ℕ := Program.timePolynomial (staged m T accept)+
  Stage.timePolynomial m T accept+Polynomial.C 1
def time (word : List (InputSymbol m)) (packets : List Bool) : ℕ :=
  (timePolynomial m T accept).eval (raw m T accept word packets).length

/-- Missing ordinary consumer of the existing actual statement compiler.
The source step h is consumed, rather than posited as compiler correctness. -/
theorem compiled_step (c d : (staged m T accept).Config)
    (h : (staged m T accept).core.step c = some d) :
    (Compiler.computer (staged m T accept)).step (Compiler.cfg (staged m T accept) c) =
      some (Compiler.cfg (staged m T accept) d) := by
  rcases c with ⟨label,v,S⟩
  cases label with
  | none => simp [FinTM2.step,TM2.step] at h
  | some l =>
    have hd : TM2.stepAux ((staged m T accept).core.m l) v S = d := Option.some.inj h
    change some (TM2.stepAux (Compiler.statement (staged m T accept) _)
      (Block.clear (staged m T accept) v) (Code.tapes (staged m T accept) S)) = _
    rw [Compiler.statement_stepAux,hd]

theorem compiled_run (n : ℕ) (c d : (staged m T accept).Config)
    (h : (fun p => p.bind (staged m T accept).core.step)^[n] (some c) = some d) :
    (fun p => p.bind (Compiler.computer (staged m T accept)).step)^[n]
      (some (Compiler.cfg (staged m T accept) c)) = some (Compiler.cfg (staged m T accept) d) := by
  induction n generalizing d with
  | zero => have hd := Option.some.inj h; subst d; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    cases hp : (fun p => p.bind (staged m T accept).core.step)^[n] (some c) with
    | none => rw [hp] at h; cases h
    | some previous =>
      have hs : (staged m T accept).core.step previous = some d := by simpa only [hp,Option.bind_some] using h
      rw [ih previous hp,Option.bind_some]
      exact compiled_step m T accept previous d hs

/-- Same raw bytes, transported only by the existing finite label/state
restatement producer. Γinput≃Bool is never instantiated. -/
theorem prepare (word : List (InputSymbol m)) (packets : List Bool) :
    (fun p => p.bind (native m T accept).core.step)^[
      Program.steps (staged m T accept) (word.length+packets.length)]
      (some (initList (native m T accept).core (raw m T accept word packets))) =
        some (Output.entry m T accept
          (initList (staged m T accept).core (taggedWord m word packets))) := by
  have hr := Source.initialize_step m T accept word packets []
  have ht := BooleanOpcode.NativeFinish.empty_run_to_active (Output.old m T accept) _ _ _ hr rfl
  have hn := Output.HS.restate_run (fun _ : Output.Stack m T accept => Bool)
    (Output.states m T accept) some (some none) (Output.old m T accept).core.m
    (native m T accept).core.m (Output.program_at_label m T accept false) _ _ _ ht
  convert hn using 1 <;> rfl

/-- The produced original staging run is compiled, embedded into the same
source tapes, then transported to the installed decoder successor. -/
theorem staging_run (word : List (InputSymbol m)) (packets : List Bool) :
    (fun p => p.bind (native m T accept).core.step)^[
      (Stage.outputs m T accept word packets).steps]
      (some (Output.entry m T accept
        (initList (staged m T accept).core (taggedWord m word packets)))) =
        some (Output.entry m T accept
          (haltList (staged m T accept).core [Output.symbol m T accept (verdict m T accept word packets)])) := by
  have hc := compiled_run m T accept _ _ _ (Stage.outputs m T accept word packets).evals_in_steps
  have hf := embed_run (Program.layout (staged m T accept)) (Program.states (staged m T accept))
    Sum.inr none (Compiler.computer (staged m T accept)).m (Output.old m T accept).core.m
    (fun _ => rfl) _ _ _ hc
  have hn := Output.HS.restate_run (fun _ : Output.Stack m T accept => Bool)
    (Output.states m T accept) some (some none) (Output.old m T accept).core.m
    (native m T accept).core.m (Output.program_at_label m T accept false) _ _ _ hf
  exact hn

/-- The upper bound uses serialized input length L. Its source term still
executes the old clock T(N), not a replacement clock T(L). -/
theorem total_steps_le (word : List (InputSymbol m)) (packets : List Bool) :
    1+(Stage.outputs m T accept word packets).steps+
      Program.steps (staged m T accept) (word.length+packets.length) ≤ time m T accept word packets := by
  have hp := Source.initialize_time m T accept word packets
  have hw : 1 ≤ rawWidth m T accept := rawWidth_pos m T accept
  have hl : word.length+packets.length ≤ (raw m T accept word packets).length := by
    rw [raw_length]
    simpa using Nat.mul_le_mul_right (word.length+packets.length) hw
  have hs := (Stage.outputs m T accept word packets).steps_le_m.trans
    (natPolynomial_eval_mono (Stage.timePolynomial m T accept) hl)
  have ht := Nat.add_le_add hp hs
  simpa [time,timePolynomial,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Nat.add_le_add_right ht 1

/-- Actual whole clean output for every packet word, including illegal,
short and long packets. The verdict is derived by the old finite programme. -/
def outputs (word : List (InputSymbol m)) (packets : List Bool) :
    TM2OutputsInTime (native m T accept).core (raw m T accept word packets)
      (some [verdict m T accept word packets]) (time m T accept word packets) where
  steps := 1+(Stage.outputs m T accept word packets).steps+
    Program.steps (staged m T accept) (word.length+packets.length)
  evals_in_steps := by
    change (fun p => p.bind (native m T accept).core.step)^[
      1+(Stage.outputs m T accept word packets).steps+
      Program.steps (staged m T accept) (word.length+packets.length)]
      (some (initList (native m T accept).core (raw m T accept word packets))) =
      some (haltList (native m T accept).core [verdict m T accept word packets])
    rw [Function.iterate_add_apply,prepare m T accept,Function.iterate_add_apply,staging_run m T accept]
    simpa only [Function.iterate_one,Option.bind_some] using
      Output.decoder_step m T accept (verdict m T accept word packets)
  steps_le_m := total_steps_le m T accept word packets

/-- Deterministic branches are finite control tests. They consume no path
choice; the halted state has exactly its unique None self-edge. -/
theorem run_eq_hold (n : ℕ) (log : List Bool) (c : (native m T accept).Config) :
    (native m T accept).run n (log,c) =
      some (log,(Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (native m T accept).core)^[n] c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    have ha : (native m T accept).advance (log,c) =
        some (log,Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (native m T accept).core c) := by
      cases hl : c.l <;> simp [BinaryMachine.advance,BinaryMachine.step,Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep,
        hl,Output.machine]
    rw [BinaryMachine.run,ha,Option.bind_some,ih,Function.iterate_succ_apply]

theorem run_at_bound (word : List (InputSymbol m)) (packets log : List Bool) :
    (native m T accept).run (time m T accept word packets)
      (log,initList (native m T accept).core (raw m T accept word packets)) =
        some (log,haltList (native m T accept).core [verdict m T accept word packets]) := by
  rw [run_eq_hold,Holant.LocalDrafts.CountingHardness.VerifierRun.outputs_at_bound (native m T accept).core _ _ _
    (outputs m T accept word packets)]

theorem halt_value_injective : Function.Injective (fun value : Bool =>
    haltList (native m T accept).core [value]) := by
  intro a b h
  have hs := congrArg (fun c : (native m T accept).Config => c.stk (native m T accept).core.k₁) h
  have hw : [a] = [b] := by simpa [haltList] using hs
  exact (List.cons.inj hw).1

/-- Sole complete physical criterion. All clocks, preparation and decoding
are internally produced. The right side names the original machine's actual
bounded path, packet bytes, halt and its given finite accepting-control table. -/
theorem native_accepts_iff (word : List (InputSymbol m)) (packets : List Bool) :
    (native m T accept).run (time m T accept word packets)
      ([],initList (native m T accept).core (raw m T accept word packets)) =
        some ([],haltList (native m T accept).core [true]) ↔
      ∃ tokens d, tokens.length = T.eval word.length ∧ packets = tokens.flatMap Packet.encode ∧
        m.TraceValid tokens (initList m.core word) d ∧ d.l = none ∧ accept d.var = true := by
  rw [run_at_bound]
  constructor
  · intro h
    have hc := congrArg Prod.snd (Option.some.inj h)
    exact (Stage.packet_accepts_iff m accept _ _ _).mp (halt_value_injective m T accept hc)
  · intro h
    have hv := (Stage.packet_accepts_iff m accept _ _ _).mpr h
    change verdict m T accept word packets = true at hv
    rw [hv]

/-- The real ordinary clean true output has the same criterion, even when
the source finished earlier than its advertised bound. -/
theorem physical_accepts_iff (word : List (InputSymbol m)) (packets : List Bool) :
    (∃ n, (fun p => p.bind (native m T accept).core.step)^[n]
      (some (initList (native m T accept).core (raw m T accept word packets))) =
        some (haltList (native m T accept).core [true])) ↔
      ∃ tokens d, tokens.length = T.eval word.length ∧ packets = tokens.flatMap Packet.encode ∧
        m.TraceValid tokens (initList m.core word) d ∧ d.l = none ∧ accept d.var = true := by
  constructor
  · rintro ⟨n,hr⟩
    have ht := Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some (native m T accept).core n _ _ hr
    have hb := Holant.LocalDrafts.CountingHardness.VerifierRun.outputs_at_bound (native m T accept).core _ _ _ (outputs m T accept word packets)
    let f := Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (native m T accept).core
    have h₁ : f^[n+time m T accept word packets]
        (initList (native m T accept).core (raw m T accept word packets)) =
          haltList (native m T accept).core [verdict m T accept word packets] := by
      rw [Function.iterate_add_apply,hb]
      exact Function.iterate_fixed (f := f) rfl n
    have h₂ : f^[n+time m T accept word packets]
        (initList (native m T accept).core (raw m T accept word packets)) =
          haltList (native m T accept).core [true] := by
      rw [Nat.add_comm n,Function.iterate_add_apply,ht]
      exact Function.iterate_fixed (f := f) rfl _
    have hv := halt_value_injective m T accept (h₁.symm.trans h₂)
    exact (Stage.packet_accepts_iff m accept _ _ _).mp hv
  · intro h
    have hv := (Stage.packet_accepts_iff m accept _ _ _).mpr h
    refine ⟨(outputs m T accept word packets).steps,?_⟩
    have he := (outputs m T accept word packets).evals_in_steps
    change (fun p => p.bind (native m T accept).core.step)^[(outputs m T accept word packets).steps]
      (some (initList (native m T accept).core (raw m T accept word packets))) =
      some (haltList (native m T accept).core [verdict m T accept word packets]) at he
    change verdict m T accept word packets = true at hv
    exact he.trans (congrArg (fun value => some (haltList (native m T accept).core [value])) hv)

/-- Full native physical paths are canonical None tokens, including all
preparation, true/false source cleanup, decoder and early-halt padding. -/
theorem canonical_trace (word : List (InputSymbol m)) (packets : List Bool) :
    (native m T accept).TraceValid (List.replicate (time m T accept word packets) none)
      (initList (native m T accept).core (raw m T accept word packets))
      (haltList (native m T accept).core [verdict m T accept word packets]) := by
  obtain ⟨xs,hlen,hlog,ht⟩ := (native m T accept).run_trace _ _ _
    (run_at_bound m T accept word packets [])
  have hz : xs.filterMap id = [] := by simpa only [List.append_nil] using hlog
  rw [BooleanOpcode.NativeExecution.filterMap_empty xs hz,hlen] at ht
  exact ht

/-- No other physical tokens can accompany the same prepared source or
terminal. This recovers uniqueness from the actual run, not a padding law. -/
theorem trace_tokens_unique (tokens : List (Option Bool)) (c d : (native m T accept).Config)
    (h : (native m T accept).TraceValid tokens c d) :
    tokens = List.replicate tokens.length none := by
  have hr := ((native m T accept).reify_trace tokens c d h).1
  rw [run_eq_hold] at hr
  have hz : tokens.filterMap id = [] := congrArg Prod.fst (Option.some.inj hr)
  exact BooleanOpcode.NativeExecution.filterMap_empty tokens hz

def capacityPolynomial : Polynomial ℕ := Polynomial.X+
  timePolynomial m T accept*Polynomial.C (native m T accept).pushBudget
def primitivePolynomial : Polynomial ℕ := timePolynomial m T accept*
  Polynomial.C (native m T accept).primitiveBudget
def bitsPolynomial : Polynomial ℕ := Polynomial.C (native m T accept).controlBits+
  capacityPolynomial m T accept*Polynomial.C (native m T accept).symbolWidths
def internalBitsPolynomial : Polynomial ℕ := Polynomial.C (native m T accept).controlBits+
  (capacityPolynomial m T accept+Polynomial.C (native m T accept).primitiveBudget)*
    Polynomial.C (native m T accept).symbolWidths

theorem prefix_capacity (input log : List Bool) (j : ℕ)
    (next : List Bool × (native m T accept).Config)
    (hj : j ≤ (timePolynomial m T accept).eval input.length)
    (hr : (native m T accept).run j (log,initList (native m T accept).core input) = some next) :
    ∀ k, (next.2.stk k).length ≤ (capacityPolynomial m T accept).eval input.length := by
  have hi : ∀ k, ((initList (native m T accept).core input).stk k).length ≤ input.length := by
    intro k; by_cases hk : k = (native m T accept).core.k₀ <;> simp [initList,hk]
  have hs := (native m T accept).run_stack_bound j _ _ input.length hi hr
  intro k
  exact (hs k).trans (by simpa [capacityPolynomial] using (Nat.add_le_add_left (Nat.mul_le_mul_right (native m T accept).pushBudget hj) input.length))

theorem actual_prefix (word : List (InputSymbol m)) (packets log : List Bool) (j : ℕ)
    (hj : j ≤ time m T accept word packets) :
    ∃ next, (native m T accept).run j
      (log,initList (native m T accept).core (raw m T accept word packets)) = some next ∧
      (∀ k, (next.2.stk k).length ≤ (capacityPolynomial m T accept).eval (raw m T accept word packets).length) ∧
      (native m T accept).primitiveCost j
        (log,initList (native m T accept).core (raw m T accept word packets)) ≤
          (primitivePolynomial m T accept).eval (raw m T accept word packets).length ∧
      (native m T accept).codedStorageBits next.2 ≤
        (bitsPolynomial m T accept).eval (raw m T accept word packets).length := by
  obtain ⟨next,hr⟩ := (native m T accept).prefix_exists _ _ _ _
    (run_at_bound m T accept word packets log) hj
  have hs := prefix_capacity m T accept _ _ _ next hj hr
  have hp := ((native m T accept).primitiveCost_le j (log,initList (native m T accept).core (raw m T accept word packets))).trans (by
    simpa [primitivePolynomial,time] using Nat.mul_le_mul_right (native m T accept).primitiveBudget hj)
  have hb := ((native m T accept).codedStorageBits_le next.2).trans (by
    simpa [bitsPolynomial] using (native m T accept).storageBits_le next.2 _ hs)
  exact ⟨next,hr,hs,by simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C,raw_length] using hp,by simpa only [bitsPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,raw_length] using hb⟩

theorem internal_prefix (input log : List Bool) (j : ℕ)
    (next : List Bool × (native m T accept).Config)
    (hj : j < (timePolynomial m T accept).eval input.length)
    (hr : (native m T accept).run j (log,initList (native m T accept).core input) = some next)
    (l : (native m T accept).core.Λ) (hl : next.2.l = some l) (alternate : Bool)
    (n : ℕ) (v : (native m T accept).core.σ) (S : (native m T accept).core.K → List Bool)
    (hp : BooleanOpcode.NativeExecution.PrimitivePrefix (Output.program m T accept alternate l)
      next.2.var next.2.stk n v S) (control : Option ((native m T accept).core.Λ)) :
    (native m T accept).primitiveCost j (log,initList (native m T accept).core input)+(n+1) ≤
      (primitivePolynomial m T accept).eval input.length ∧
    (native m T accept).codedStorageBits ⟨control,v,S⟩ ≤
      (internalBitsPolynomial m T accept).eval input.length := by
  have hc := BooleanOpcode.NativeExecution.primitive_prefix_cost _ _ _ _ _ _ hp
  have hn : n+1 ≤ (native m T accept).primitiveBudget := by
    cases alternate with
    | false => exact (Nat.add_le_add_right hc 1).trans ((native m T accept).core_budget_le l)
    | true => exact (Nat.add_le_add_right hc 1).trans ((native m T accept).alternate_budget_le l)
  constructor
  · have he := Nat.add_le_add ((native m T accept).primitiveCost_le j (log,initList (native m T accept).core input)) hn
    have ht := Nat.mul_le_mul_right (native m T accept).primitiveBudget (Nat.succ_le_of_lt hj)
    simp only [Nat.succ_mul] at ht
    exact he.trans (by simpa [primitivePolynomial] using ht)
  · have hs := prefix_capacity m T accept input log j next (Nat.le_of_lt hj) hr
    have hu := BooleanOpcode.NativeExecution.primitive_prefix_capacity _ _ _ _ _ _ hp _ hs
    have hS : ∀ k, (S k).length ≤ (capacityPolynomial m T accept).eval input.length+
        (native m T accept).primitiveBudget := by
      intro k
      exact (hu k).trans (Nat.add_le_add_left ((Nat.le_add_right n 1).trans hn) _)
    exact ((native m T accept).codedStorageBits_le _).trans (by simpa [internalBitsPolynomial] using ((native m T accept).storageBits_le ⟨control,v,S⟩ _ hS))

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralAlphabetInput.NativeExecution
