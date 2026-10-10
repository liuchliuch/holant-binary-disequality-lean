import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Execution

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Total packet checking and actual whole-program outputs.
`packetEval` is a mathematical specification by a bounded recursion, not an
instruction. The execution theorem below proves this specification from the
finite program on every packet word, including illegal, short and long words. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
open Turing Computability Holant.Complexity BinaryCompose
open scoped BigOperators
variable (m : BinaryMachine) (T : Polynomial ℕ) (acceptControl : m.core.σ → Bool)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k
local instance (k : Stack m T) : Fintype (Alphabet m T k) :=
  (deterministic m T (fun _ => false)).alphabets k

def packetEval : ℕ → List Bool → m.Config → Bool
  | 0,word,c => terminalVerdict m acceptControl word c
  | n+1,word,c => (Packet.decode word.head? word.tail.head?).elim false (fun token =>
      (m.step token c).elim false (fun d => packetEval n word.tail.tail d))

theorem arbitrary_guarded_round (count : ℕ) (word : List Bool) (c : m.Config) :
    (fun p => p.bind (computer m T acceptControl).step)^[3]
      (some (readyCfg m T acceptControl (count+1) word c)) =
      some (match Packet.decode word.head? word.tail.head? with
        | none => rejectedCfg m T acceptControl count word.head? word.tail.head? word.tail.tail c
        | some token => (m.step token c).elim
            (rejectedCfg m T acceptControl count word.head? word.tail.head? word.tail.tail c)
            (readyCfg m T acceptControl count word.tail.tail)) := by
  simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,Option.bind_some,
    first_with_clock,second_with_clock,execute_with_clock]
  rfl

theorem rejected_run (count : ℕ) (first second : Option Bool) (word : List Bool) (c : m.Config) :
    (fun p => p.bind (computer m T acceptControl).step)^[1]
      (some (rejectedCfg m T acceptControl count first second word c)) =
        some (cleanupCfg m T acceptControl false
          (rejectedCfg m T acceptControl count first second word c).stk) := by
  simpa using reject_cleanup m T acceptControl count first second word c

/-- Produces a real cleanup entry and its actual time for every bit word.
There is no trajectory, terminal state or verifier correctness premise. -/
theorem packet_run (count : ℕ) (word : List Bool) (c : m.Config) :
    ∃ t, t ≤ 3*count+1 ∧ ∃ S,
      (fun p => p.bind (computer m T acceptControl).step)^[t]
        (some (readyCfg m T acceptControl count word c)) =
          some (cleanupCfg m T acceptControl (packetEval m acceptControl count word c) S) := by
  induction count generalizing word c with
  | zero =>
    exact ⟨1,by simp,(readyCfg m T acceptControl 0 word c).stk,
      by simpa only [packetEval, Function.iterate_one, Option.bind_some] using clock_eof m T acceptControl word c⟩
  | succ count ih =>
    have hr := arbitrary_guarded_round m T acceptControl count word c
    cases hd : Packet.decode word.head? word.tail.head? with
    | none =>
      refine ⟨4,by omega,
        (rejectedCfg m T acceptControl count word.head? word.tail.head? word.tail.tail c).stk,?_⟩
      rw [show 4 = 1+3 by rfl,Function.iterate_add_apply,hr,hd]
      simpa only [packetEval,hd,Option.elim_none] using
        rejected_run m T acceptControl count word.head? word.tail.head? word.tail.tail c
    | some token =>
      cases hs : m.step token c with
      | none =>
        refine ⟨4,by omega,
          (rejectedCfg m T acceptControl count word.head? word.tail.head? word.tail.tail c).stk,?_⟩
        rw [show 4 = 1+3 by rfl,Function.iterate_add_apply,hr,hd]
        simp only [hs, Option.elim_none]
        simpa only [packetEval,hd,hs,Option.elim_some,Option.elim_none] using
          rejected_run m T acceptControl count word.head? word.tail.head? word.tail.tail c
      | some d =>
        obtain ⟨t,ht,S,hrun⟩ := ih word.tail.tail d
        refine ⟨t+3,by omega,S,?_⟩
        rw [Function.iterate_add_apply,hr,hd]
        simp only [hs, Option.elim_some]
        simpa only [packetEval,hd,hs,Option.elim_some] using hrun

def beforeCleanup : Polynomial ℕ :=
  2*Polynomial.X+3+(clockComputes T).time+3*T+1

def beforeCapacity : Polynomial ℕ :=
  Polynomial.X+beforeCleanup T*Polynomial.C (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (computer m T acceptControl))

def timePolynomial : Polynomial ℕ :=
  beforeCleanup T+
    Polynomial.C (Fintype.card (Stack m T))*
      (Polynomial.C (Fintype.card (Stack m T))*beforeCapacity m T acceptControl+1)+1

theorem input_to_cleanup (word : List (m.core.Γ m.core.k₀)) (bits : List Bool) :
    ∃ t, t ≤ (beforeCleanup T).eval (word.length+bits.length) ∧ ∃ S,
      (fun p => p.bind (computer m T acceptControl).step)^[t]
        (some (initList (computer m T acceptControl) (word.map Sum.inl++bits.map Sum.inr))) =
          some (cleanupCfg m T acceptControl
            (packetEval m acceptControl (T.eval word.length) bits (initList m.core word)) S) := by
  obtain ⟨t,ht,S,hr⟩ := packet_run m T acceptControl (T.eval word.length) bits (initList m.core word)
  let clockSteps := ((clockComputes T).outputs word.length).steps
  have hclock := clock_run m T acceptControl word bits
  rw [clock_terminal] at hclock
  have hstage := raw_staging m T acceptControl word bits
  refine ⟨t+clockSteps+(2*(word.length+bits.length)+3),?_,S,?_⟩
  · have hc : clockSteps ≤ (clockComputes T).time.eval (word.length+bits.length) :=
      ((clockComputes T).outputs word.length).steps_le_m.trans
        (natPolynomial_eval_mono _ (by
          simp only [Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters.unary,
            Holant.Complexity.GraphPreprocessing.UnaryBinary.unaryEncoding, List.length_replicate]
          omega))
    have hT := natPolynomial_eval_mono T (Nat.le_add_right word.length bits.length)
    simp only [beforeCleanup,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one]
    omega
  · rw [Function.iterate_add_apply,Function.iterate_add_apply,hstage,hclock,hr]

/-- Compose a produced actual cleanup entry. The whole verifier supplies hr
from input_to_cleanup; malformed headers supply it from real scanning pops. -/
theorem complete_cleanup_exists (input : List (m.core.Γ m.core.k₀ ⊕ Bool))
    (value : Bool) (t : ℕ) (S : ∀ k, List (Alphabet m T k))
    (ht : t ≤ (beforeCleanup T).eval input.length)
    (hr : (fun p => p.bind (computer m T acceptControl).step)^[t]
      (some (initList (computer m T acceptControl) input)) =
        some (cleanupCfg m T acceptControl value S)) :
    Nonempty (TM2OutputsInTime (computer m T acceptControl) input (some [Sum.inr value])
      ((timePolynomial m T acceptControl).eval input.length)) := by
  obtain ⟨s,hs,hclean⟩ := cleanup_run m T acceptControl value S
  have hhold := Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some (computer m T acceptControl) t _ _ hr
  have hS : ∀ k, (S k).length ≤ (beforeCapacity m T acceptControl).eval input.length := by
    intro k
    have h := Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound (computer m T acceptControl) input t k
    rw [hhold] at h
    have hmul := Nat.mul_le_mul_right (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (computer m T acceptControl)) ht
    simpa only [cleanupCfg,HeterogeneousSum.restateCfg,Cleanup.cfg,
      beforeCapacity,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
      Polynomial.eval_C] using h.trans (Nat.add_le_add_left hmul input.length)
  have hsum : (∑ k, (S k).length) ≤ Fintype.card (Stack m T)*
      (beforeCapacity m T acceptControl).eval input.length := by
    simpa using Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hS k)
  refine ⟨{ steps := s+t, evals_in_steps := ?_, steps_le_m := ?_ }⟩
  · change (fun p : Option (computer m T acceptControl).Cfg => p.bind (computer m T acceptControl).step)^[s+t]
      (some (initList (computer m T acceptControl) input)) =
        some (haltList (computer m T acceptControl) [Sum.inr value])
    rw [Function.iterate_add_apply,hr]
    exact hclean
  · have hcleanBound := Nat.mul_le_mul_left (Fintype.card (Stack m T))
      (Nat.add_le_add_right hsum 1)
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_one]
    omega

/-- Actual output for all witness words. Reject paths use the same physical
cleaner and reset every stack/state, rather than halting with leftover data. -/
theorem outputs_exists (word : List (m.core.Γ m.core.k₀)) (bits : List Bool) :
    Nonempty (TM2OutputsInTime (computer m T acceptControl) (word.map Sum.inl++bits.map Sum.inr)
      (some [Sum.inr (packetEval m acceptControl (T.eval word.length) bits (initList m.core word))])
      ((timePolynomial m T acceptControl).eval (word.length+bits.length))) := by
  obtain ⟨t,ht,S,hr⟩ := input_to_cleanup m T acceptControl word bits
  simpa only [List.length_append,List.length_map] using
    complete_cleanup_exists m T acceptControl (word.map Sum.inl++bits.map Sum.inr)
      (packetEval m acceptControl (T.eval word.length) bits (initList m.core word)) t S
      (by simpa only [List.length_append,List.length_map] using ht) hr

def outputs (word : List (m.core.Γ m.core.k₀)) (bits : List Bool) :
    TM2OutputsInTime (computer m T acceptControl) (word.map Sum.inl++bits.map Sum.inr)
      (some [Sum.inr (packetEval m acceptControl (T.eval word.length) bits (initList m.core word))])
      ((timePolynomial m T acceptControl).eval (word.length+bits.length)) :=
  Classical.choice (outputs_exists m T acceptControl word bits)

def verifier {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀)) :
    PolyTime (encodingProd ea (encodingList Bool)) (taggedBoolEncoding (m.core.Γ m.core.k₀))
      (fun p : α×List Bool =>
        packetEval m acceptControl (T.eval (ea.encode p.1).length) p.2 (initList m.core (ea.encode p.1))) where
  tm := computer m T acceptControl
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial m T acceptControl
  outputsFun p := by
    simpa only [encodingProd,encodingList,taggedBoolEncoding,List.map_id,
      List.length_append,List.length_map, Equiv.refl, id_eq] using outputs m T acceptControl (ea.encode p.1) p.2
  finiteAlphabets := (deterministic m T acceptControl).alphabets

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
