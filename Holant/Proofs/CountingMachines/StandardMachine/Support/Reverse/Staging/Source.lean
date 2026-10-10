import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Resources

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Sole consumer entry for the actual reverse wrapper.
Inputs are a fixed actual BinaryMachine, its finite accepting-control table,
a polynomial clock and the original input encoding. No Computes, accepted
trajectory, desired flag, count equality or model-equivalence premise is used.
The count is explicitly the original bounded canonical TM2 path count. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Source
open Turing Computability Holant.Complexity
variable (m : BinaryMachine) (T : Polynomial ℕ) (acceptControl : m.core.σ → Bool)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k
local instance (k : Program.Stack m T) : Fintype (Program.Alphabet m T k) :=
  (Program.deterministic m T (fun _ => false)).alphabets k

abbrev machine := Program.computer m T acceptControl
def reverseWitness {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀)) :
    SharpPWitness ea (Program.pathCount m acceptControl ea T) :=
  Program.sharpPWitness m acceptControl ea T

theorem bounded_inSharpP {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀)) :
    InSharpP ea (Program.pathCount m acceptControl ea T) :=
  ⟨reverseWitness m T acceptControl ea⟩

def accepted_equiv {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀)) (a : α) :
    Program.AcceptedBits m acceptControl (T.eval (ea.encode a).length) (initList m.core (ea.encode a)) ≃
      Program.AcceptedPath m acceptControl (T.eval (ea.encode a).length) (initList m.core (ea.encode a)) :=
  Program.acceptedEquiv m acceptControl _ _

/-- The accepted token vector reifies to the same original nondeterministic
program, with exactly its actual split choices consumed and no leftover log.
The original producer also recovers the entire canonical token vector. -/
theorem path_execution {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀)) (a : α)
    (p : Program.AcceptedPath m acceptControl (T.eval (ea.encode a).length)
      (initList m.core (ea.encode a))) :
    ∃ d, m.run (T.eval (ea.encode a).length)
        ((List.ofFn p.val).filterMap id,initList m.core (ea.encode a)) = some ([],d) ∧
      m.tokensOfRun (T.eval (ea.encode a).length)
        ((List.ofFn p.val).filterMap id,initList m.core (ea.encode a)) = List.ofFn p.val ∧
      d.l = none ∧ acceptControl d.var = true := by
  obtain ⟨d,ht,hd,ha⟩ := p.property
  have hr := m.reify_trace (List.ofFn p.val) _ d ht
  exact ⟨d,by simpa only [List.length_ofFn] using hr.1,
    by simpa only [List.length_ofFn] using hr.2,hd,ha⟩

theorem clean_output_unique (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (a b : Bool) (t u : ℕ)
    (ha : (fun p => p.bind (machine m T acceptControl).step)^[t]
      (some (initList (machine m T acceptControl) input)) =
        some (haltList (machine m T acceptControl) [Sum.inr a]))
    (hb : (fun p => p.bind (machine m T acceptControl).step)^[u]
      (some (initList (machine m T acceptControl) input)) =
        some (haltList (machine m T acceptControl) [Sum.inr b])) : a = b := by
  have h₁ := Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some (machine m T acceptControl) t _ _ ha
  have h₂ := Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some (machine m T acceptControl) u _ _ hb
  have hout : haltList (machine m T acceptControl) [Sum.inr a] =
      haltList (machine m T acceptControl) [Sum.inr b] := by
    rcases Nat.le_total t u with htu | hut
    · have hp : (Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (machine m T acceptControl))^[u]
          (initList (machine m T acceptControl) input) =
            haltList (machine m T acceptControl) [Sum.inr a] := by
        rw [show u = (u-t)+t by omega,Function.iterate_add_apply,h₁]
        exact Function.iterate_fixed (f := Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (machine m T acceptControl)) rfl _
      exact hp.symm.trans h₂
    · have hp : (Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (machine m T acceptControl))^[t]
          (initList (machine m T acceptControl) input) =
            haltList (machine m T acceptControl) [Sum.inr b] := by
        rw [show t = (t-u)+u by omega,Function.iterate_add_apply,h₂]
        exact Function.iterate_fixed (f := Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (machine m T acceptControl)) rfl _
      exact h₁.symm.trans hp
  have hw := congrArg (fun c : (machine m T acceptControl).Cfg => c.stk (Program.raw m T)) hout
  change ([Sum.inr a] : List (m.core.Γ m.core.k₀ ⊕ Bool)) = [Sum.inr b] at hw
  exact Sum.inr.inj (List.cons.inj hw).1


/-- Physical acceptance starts on the one original tagged input stack and
ends in the actual whole machine's clean halt. Both implications consume real
execution; the right side consists of original source edges and original halt.
-/
theorem physical_accepts_iff (word : List (m.core.Γ m.core.k₀)) (bits : List Bool) :
    (∃ t, (fun p => p.bind (machine m T acceptControl).step)^[t]
      (some (initList (machine m T acceptControl) (word.map Sum.inl++bits.map Sum.inr))) =
        some (haltList (machine m T acceptControl) [Sum.inr true])) ↔
      ∃ tokens d, tokens.length = T.eval word.length ∧ bits = tokens.flatMap Packet.encode ∧
        m.TraceValid tokens (initList m.core word) d ∧ d.l = none ∧ acceptControl d.var = true := by
  constructor
  · rintro ⟨t,hr⟩
    have out := Program.outputs m T acceptControl word bits
    have hv := clean_output_unique m T acceptControl _ _ true out.steps t out.evals_in_steps hr
    exact (Program.packet_accepts_iff m acceptControl _ _ _).mp hv
  · intro hp
    have hv := (Program.packet_accepts_iff m acceptControl _ _ _).mpr hp
    refine ⟨(Program.outputs m T acceptControl word bits).steps, ?_⟩
    have ho := (Program.outputs m T acceptControl word bits).evals_in_steps
    simp only [hv, Option.map_some] at ho
    convert ho using 1 <;> rfl

theorem wrong_length_rejected (n : ℕ) (bits : List Bool) (c : m.Config)
    (h : bits.length ≠ 2*n) : Program.packetEval m acceptControl n bits c = false := by
  cases he : Program.packetEval m acceptControl n bits c with
  | false => rfl
  | true =>
    obtain ⟨tokens,d,hlen,hword,ht,hd,ha⟩ :=
      (Program.packet_accepts_iff m acceptControl n bits c).mp he
    apply False.elim
    apply h
    rw [hword,Program.encoded_length,hlen]

theorem illegal_packet_rejected (n : ℕ) (rest : List Bool) (c : m.Config) :
    Program.packetEval m acceptControl (n+1) (false::true::rest) c = false := by
  simp only [Program.packetEval,List.head?_cons,List.tail_cons,Packet.malformed,Option.elim_none]

theorem forbidden_packet_rejected (n : ℕ) (token : Option Bool) (rest : List Bool) (c : m.Config)
    (h : m.step token c = none) :
    Program.packetEval m acceptControl (n+1) (Packet.encode token++rest) c = false := by
  rw [Program.packetEval,Program.decode_encoded,Option.elim_some,h,Option.elim_none]

/-- Malformed tag order goes to the same real false cleaner. This entry starts
at the actual scan prefix, so it also applies after any previously proved pops.
-/
theorem bad_header_clean (a : m.core.Γ m.core.k₀)
    (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (original : List (m.core.Γ m.core.k₀)) (bits : List Bool) (n : ℕ) :
    ∃ t, (fun p => p.bind (machine m T acceptControl).step)^[t]
      (some (Program.scanCfg m T acceptControl true (.inl a::input) original bits n)) =
        some (haltList (machine m T acceptControl) [Sum.inr false]) := by
  let S := Function.update
    (Program.scanCfg m T acceptControl true (.inl a::input) original bits n).stk (Program.raw m T) input
  obtain ⟨t,ht,hr⟩ := Program.cleanup_run m T acceptControl false S
  refine ⟨t+1,?_⟩
  rw [Function.iterate_succ_apply,Option.bind_some,Program.scan_bad_order]
  exact hr

/-- Complete initial-input rejection for the first out-of-order original tag,
after an arbitrary original prefix and a nonempty packet-field prefix. No
decoded field, prepared tape or accepted state is a caller-supplied initializer.
-/
theorem raw_bad_header_timed (word : List (m.core.Γ m.core.k₀))
    (first : Bool) (bits : List Bool) (a : m.core.Γ m.core.k₀)
    (suffix : List (m.core.Γ m.core.k₀ ⊕ Bool)) :
    Nonempty (TM2OutputsInTime (machine m T acceptControl)
      (word.map Sum.inl++(Sum.inr first::(bits.map Sum.inr++(Sum.inl a::suffix))))
      (some [Sum.inr false]) ((Program.timePolynomial m T acceptControl).eval
        (word.length+bits.length+suffix.length+2))) := by
  let input := word.map Sum.inl++(Sum.inr first::(bits.map Sum.inr++(Sum.inl a::suffix)))
  let S := Function.update
    (Program.scanCfg m T acceptControl true (Sum.inl a::suffix) word.reverse
      (bits.reverse++[first]) word.length).stk (Program.raw m T) suffix
  have hleft := Program.scan_original_prefix m T acceptControl word []
    (Sum.inr first::(bits.map Sum.inr++(Sum.inl a::suffix))) [] 0
  have hright := Program.scan_right_prefix m T acceptControl bits [first]
    (Sum.inl a::suffix) word.reverse word.length
  simp only [List.append_nil,Nat.zero_add] at hleft
  have hpre : (fun p => p.bind (machine m T acceptControl).step)^[1+(bits.length+1)+word.length]
      (some (initList (machine m T acceptControl) input)) =
        some (Program.cleanupCfg m T acceptControl false S) := by
    dsimp only [input, machine]
    rw [← Program.initial_raw,Function.iterate_add_apply,hleft,Function.iterate_add_apply,
      Function.iterate_one,Function.iterate_succ_apply,Option.bind_some,
      Program.scan_right,hright,Option.bind_some]
    exact Program.scan_bad_order m T acceptControl a suffix word.reverse
      (bits.reverse++[first]) word.length
  have htime : 1+(bits.length+1)+word.length ≤ (Program.beforeCleanup T).eval input.length := by
    simp only [input,List.length_append,List.length_map,List.length_cons,Program.beforeCleanup,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,
      Polynomial.eval_X]
    omega
  have hlength : input.length = word.length + bits.length + suffix.length + 2 := by
    simp only [input, List.length_append, List.length_map, List.length_cons]
    omega
  have result := Program.complete_cleanup_exists m T acceptControl input false _ S htime hpre
  rw [hlength] at result
  exact result

theorem raw_bad_header_clean (word : List (m.core.Γ m.core.k₀))
    (first : Bool) (bits : List Bool) (a : m.core.Γ m.core.k₀)
    (suffix : List (m.core.Γ m.core.k₀ ⊕ Bool)) :
    ∃ t, (fun p => p.bind (machine m T acceptControl).step)^[t]
      (some (initList (machine m T acceptControl)
        (word.map Sum.inl++(Sum.inr first::(bits.map Sum.inr++(Sum.inl a::suffix)))))) =
        some (haltList (machine m T acceptControl) [Sum.inr false]) := by
  obtain ⟨run⟩ := raw_bad_header_timed m T acceptControl word first bits a suffix
  exact ⟨run.steps,run.evals_in_steps⟩

/-- Every actual macro prefix exists and carries the original-input polynomial
capacity, finite-symbol-code bits and the same real primitive observer bound.
The bound covers both accepted and rejected packet words, including cleanup.
-/
theorem actual_prefix (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (j : ℕ) (hj : j ≤ (Program.outputs m T acceptControl word bits).steps) :
    ∃ next, (fun p => p.bind (machine m T acceptControl).step)^[j]
      (some (initList (machine m T acceptControl) (word.map Sum.inl++bits.map Sum.inr))) = some next ∧
      (∀ k, (next.stk k).length ≤ (Program.capacityPolynomial m T acceptControl).eval
        (word.length+bits.length)) ∧
      (Program.deterministic m T acceptControl).codedStorageBits next ≤
        (Program.bitsPolynomial m T acceptControl).eval (word.length+bits.length) ∧
      (Program.deterministic m T acceptControl).primitiveCost j
        ([],initList (machine m T acceptControl) (word.map Sum.inl++bits.map Sum.inr)) ≤
          (Program.primitivePolynomial m T acceptControl).eval (word.length+bits.length) := by
  obtain ⟨next,hr⟩ := Program.prefix_exists m T acceptControl _ j _ _
    (Program.outputs m T acceptControl word bits).evals_in_steps hj
  exact ⟨next,hr,Program.prefix_capacity m T acceptControl word bits j next hj hr,
    Program.prefix_bits m T acceptControl word bits j next hj hr,
    Program.prefix_primitive m T acceptControl word bits j hj⟩

theorem internal_bits (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (j : ℕ) (next : (machine m T acceptControl).Cfg)
    (hj : j < (Program.outputs m T acceptControl word bits).steps)
    (hr : (fun p => p.bind (machine m T acceptControl).step)^[j]
      (some (initList (machine m T acceptControl) (word.map Sum.inl++bits.map Sum.inr))) = some next)
    (l : Program.Label m T) (u : Program.State m T) (U : ∀ k, List (Program.Alphabet m T k))
    (h : Program.InstructionPrefix m T acceptControl (Program.program m T acceptControl l)
      next.var next.stk u U) (control : Option (Program.Label m T)) :
    (Program.deterministic m T acceptControl).codedStorageBits ⟨control,u,U⟩ ≤
      (Program.bitsPolynomial m T acceptControl).eval (word.length+bits.length) :=
  Program.internal_bits m T acceptControl word bits j next hj hr l u U h control

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Source
