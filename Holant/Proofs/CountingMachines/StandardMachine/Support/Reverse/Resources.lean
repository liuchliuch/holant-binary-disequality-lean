import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Semantics
import Holant.Proofs.CountingMachines.StandardMachine.Support.Cost
import Holant.Proofs.CountingMachines.StandardMachine.Support.TimedSimulation

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Real component macro time, primitive and every-prefix
finite-code bit bounds. The starting bound is calculated from actual tapes;
neither a capacity certificate nor simulator Computes is an input.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Program
open Turing Holant.Complexity
open scoped BigOperators
variable (m : BinaryMachine)
local instance : Fintype m.core.K := m.core.kFin

def sourceCells (c : m.Config) : ℕ := ∑ k : m.core.K, (c.stk k).length
def initialBound (word : List Bool) (c : m.Config) : ℕ := word.length + sourceCells m c

/-- The actual tapes at every elementary instruction inside a TM2 statement.
The selected branch and each push/pop/peek/load use precisely stepAux's finite
functions. This mathematical observer is never an interpreter opcode.
-/
def PrimitiveTapeBound (m : BinaryMachine) : (computer m).Stmt → (computer m).σ →
    (∀ k, List ((computer m).Γ k)) → ℕ → Prop
  | .push k f q,v,S,C => (∀ j, (S j).length ≤ C) ∧
      PrimitiveTapeBound m q v (Function.update S k (f v :: S k)) C
  | .pop k f q,v,S,C => (∀ j, (S j).length ≤ C) ∧
      PrimitiveTapeBound m q (f v (S k).head?) (Function.update S k (S k).tail) C
  | .peek k f q,v,S,C => (∀ j, (S j).length ≤ C) ∧
      PrimitiveTapeBound m q (f v (S k).head?) S C
  | .load f q,v,S,C => (∀ j, (S j).length ≤ C) ∧ PrimitiveTapeBound m q (f v) S C
  | .branch f q r,v,S,C => (∀ j, (S j).length ≤ C) ∧
      if f v then PrimitiveTapeBound m q v S C else PrimitiveTapeBound m r v S C
  | .goto _,_,S,C => ∀ j, (S j).length ≤ C
  | .halt,_,S,C => ∀ j, (S j).length ≤ C

theorem primitiveTape_mono (q : (computer m).Stmt) (v : (computer m).σ)
    (S : ∀ k, List ((computer m).Γ k)) (C D : ℕ)
    (h : PrimitiveTapeBound m q v S C) (hCD : C ≤ D) :
    PrimitiveTapeBound m q v S D := by
  induction q generalizing v S with
  | push k f q ih => exact ⟨fun j => (h.1 j).trans hCD,ih _ _ h.2⟩
  | pop k f q ih => exact ⟨fun j => (h.1 j).trans hCD,ih _ _ h.2⟩
  | peek k f q ih => exact ⟨fun j => (h.1 j).trans hCD,ih _ _ h.2⟩
  | load f q ih => exact ⟨fun j => (h.1 j).trans hCD,ih _ _ h.2⟩
  | branch f q r hq hr =>
    refine ⟨fun j => (h.1 j).trans hCD,?_⟩
    cases hf : f v
    · exact hr _ _ (by simpa only [hf,ite_false,Bool.false_eq_true] using h.2)
    · exact hq _ _ (by simpa only [hf,ite_true] using h.2)
  | goto f => exact fun j => (h j).trans hCD
  | halt => exact fun j => (h j).trans hCD

theorem all_primitive_tapes (q : (computer m).Stmt) (v : (computer m).σ)
    (S : ∀ k, List ((computer m).Γ k)) (B : ℕ) (hS : ∀ k, (S k).length ≤ B) :
    PrimitiveTapeBound m q v S (B + Holant.LocalDrafts.CountingHardness.VerifierRun.pushes q) := by
  induction q generalizing v S B with
  | push k f q ih =>
    have hu : ∀ j, ((Function.update S k (f v :: S k)) j).length ≤ B+1 := by
      intro j
      by_cases hj : j = k
      · subst j; simpa using Nat.add_le_add_right (hS k) 1
      · simpa [hj] using (hS j).trans (Nat.le_add_right B 1)
    refine ⟨fun j => (hS j).trans (Nat.le_add_right _ _),?_⟩
    simpa only [Holant.LocalDrafts.CountingHardness.VerifierRun.pushes,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih v (Function.update S k (f v :: S k)) (B+1) hu
  | pop k f q ih =>
    have hu : ∀ j, ((Function.update S k (S k).tail) j).length ≤ B := by
      intro j
      by_cases hj : j = k
      · subst j
        have ht : (S k).tail.length ≤ (S k).length := by simp
        simpa using ht.trans (hS k)
      · simpa [hj] using hS j
    exact ⟨fun j => (hS j).trans (Nat.le_add_right _ _),ih _ _ B hu⟩
  | peek k f q ih => exact ⟨fun j => (hS j).trans (Nat.le_add_right _ _),ih _ S B hS⟩
  | load f q ih => exact ⟨fun j => (hS j).trans (Nat.le_add_right _ _),ih _ S B hS⟩
  | branch f q r hq hr =>
    refine ⟨fun j => (hS j).trans (Nat.le_add_right _ _),?_⟩
    cases hf : f v
    · simp only [PrimitiveTapeBound,hf,ite_false,Bool.false_eq_true]
      exact primitiveTape_mono m r v S _ _ (hr v S B hS) (by simp [Holant.LocalDrafts.CountingHardness.VerifierRun.pushes])
    · simp only [PrimitiveTapeBound,hf,ite_true]
      exact primitiveTape_mono m q v S _ _ (hq v S B hS) (by simp [Holant.LocalDrafts.CountingHardness.VerifierRun.pushes])
  | goto f => simpa only [PrimitiveTapeBound,Holant.LocalDrafts.CountingHardness.VerifierRun.pushes,Nat.add_zero] using hS
  | halt => simpa only [PrimitiveTapeBound,Holant.LocalDrafts.CountingHardness.VerifierRun.pushes,Nat.add_zero] using hS

def PrimitiveBitsBound (m : BinaryMachine) : (computer m).Stmt → (computer m).σ →
    (∀ k, List ((computer m).Γ k)) → ℕ → Prop
  | .push k f q,v,S,B =>
      (∀ l, (deterministic m).codedStorageBits ⟨l,v,S⟩ ≤ B) ∧
        PrimitiveBitsBound m q v (Function.update S k (f v :: S k)) B
  | .pop k f q,v,S,B =>
      (∀ l, (deterministic m).codedStorageBits ⟨l,v,S⟩ ≤ B) ∧
        PrimitiveBitsBound m q (f v (S k).head?) (Function.update S k (S k).tail) B
  | .peek k f q,v,S,B =>
      (∀ l, (deterministic m).codedStorageBits ⟨l,v,S⟩ ≤ B) ∧
        PrimitiveBitsBound m q (f v (S k).head?) S B
  | .load f q,v,S,B =>
      (∀ l, (deterministic m).codedStorageBits ⟨l,v,S⟩ ≤ B) ∧ PrimitiveBitsBound m q (f v) S B
  | .branch f q r,v,S,B =>
      (∀ l, (deterministic m).codedStorageBits ⟨l,v,S⟩ ≤ B) ∧
        if f v then PrimitiveBitsBound m q v S B else PrimitiveBitsBound m r v S B
  | .goto _,v,S,B => ∀ l, (deterministic m).codedStorageBits ⟨l,v,S⟩ ≤ B
  | .halt,v,S,B => ∀ l, (deterministic m).codedStorageBits ⟨l,v,S⟩ ≤ B

theorem tapes_to_bits (q : (computer m).Stmt) (v : (computer m).σ)
    (S : ∀ k, List ((computer m).Γ k)) (C : ℕ)
    (h : PrimitiveTapeBound m q v S C) :
    PrimitiveBitsBound m q v S
      ((deterministic m).controlBits + C * (deterministic m).symbolWidths) := by
  have hb (v : (computer m).σ) (S : ∀ k, List ((computer m).Γ k))
      (hS : ∀ k, (S k).length ≤ C) (l : Option (computer m).Λ) :
      (deterministic m).codedStorageBits ⟨l,v,S⟩ ≤
        (deterministic m).controlBits + C * (deterministic m).symbolWidths :=
    ((deterministic m).codedStorageBits_le _).trans
      ((deterministic m).storageBits_le _ C hS)
  induction q generalizing v S with
  | push k f q ih => exact ⟨hb v S h.1,ih _ _ h.2⟩
  | pop k f q ih => exact ⟨hb v S h.1,ih _ _ h.2⟩
  | peek k f q ih => exact ⟨hb v S h.1,ih _ _ h.2⟩
  | load f q ih => exact ⟨hb v S h.1,ih _ _ h.2⟩
  | branch f q r hq hr =>
    refine ⟨hb v S h.1,?_⟩
    cases hf : f v
    · exact hr _ _ (by simpa only [hf,ite_false,Bool.false_eq_true] using h.2)
    · exact hq _ _ (by simpa only [hf,ite_true] using h.2)
  | goto f => exact hb v S h
  | halt => exact hb v S h

local instance : Fintype (computer m).Λ := (computer m).ΛFin

theorem instruction_pushes_le (l : (computer m).Λ) :
    Holant.LocalDrafts.CountingHardness.VerifierRun.pushes ((computer m).m l) ≤ (deterministic m).pushBudget := by
  have hp : Holant.LocalDrafts.CountingHardness.VerifierRun.pushes ((computer m).m l) ≤ Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (computer m) :=
    by
      unfold Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget
      exact Finset.single_le_sum (f := fun label => Holant.LocalDrafts.CountingHardness.VerifierRun.pushes ((computer m).m label)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  exact hp.trans (Nat.le_add_right _ _)

theorem ready_bound (word : List Bool) (c : m.Config) :
    ∀ k, ((readyCfg m word c).stk k).length ≤ initialBound m word c := by
  intro k
  cases k with
  | inl k => simp [readyCfg,phaseCfg,SumStacks.merge,initialBound]
  | inr k =>
    have h : (c.stk k).length ≤ sourceCells m c :=
      by
        unfold sourceCells
        exact Finset.single_le_sum (f := fun key => (c.stk key).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    exact h.trans (by simp [readyCfg,phaseCfg,SumStacks.merge,initialBound])

theorem deterministic_advance (log : List Bool) (c : (computer m).Cfg) :
    (deterministic m).advance (log,c) =
      some (log,Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (computer m) c) := by
  rcases c with ⟨l,v,S⟩
  cases l <;> rfl

theorem deterministic_run (t : ℕ) (log : List Bool) (c : (computer m).Cfg) :
    (deterministic m).run t (log,c) =
      some (log,(Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (computer m))^[t] c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [BinaryMachine.run,deterministic_advance,Option.bind_some,ih,
      Function.iterate_succ_apply]

theorem lift_run (t : ℕ) (c d : (computer m).Cfg)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[t]
      (some c) = some d) :
    (deterministic m).run t ([],c) = some ([],d) := by
  rw [deterministic_run,Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some (computer m) t c d h]

theorem actual_prefix_exists (t j : ℕ) (c d : (computer m).Cfg)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[t]
      (some c) = some d) (hj : j ≤ t) :
    ∃ next, (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some c) = some next := by
  cases hp : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j] (some c) with
  | some next => exact ⟨next,rfl⟩
  | none =>
    have hn : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[t-j] none = none :=
      Function.iterate_fixed (f := fun p : Option (computer m).Cfg => p.bind (computer m).step)
        rfl (t-j)
    rw [show t = (t-j)+j by omega,Function.iterate_add_apply,hp,hn] at h
    cases h

/-- The macro needed by TimedSimulation, with its proof supplied by this actual
program rather than taken as a new interface premise.
-/
def timed_round (token : Option Bool) (word : List Bool) (c d : m.Config)
    (h : m.step token c = some d) :
    TimedSimulation.Witness (computer m).step
      (fun source target => target = readyCfg m word source)
      (readyCfg m (Packet.encode token ++ word) c) d 3 where
  target := readyCfg m word d
  related := rfl
  evaluation := {
    steps := 3
    evals_in_steps := round m token word c d h
    steps_le_m := le_rfl }

theorem prefix_capacity (word : List Bool) (c : m.Config) (j : ℕ)
    (next : (computer m).Cfg)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some (readyCfg m word c)) = some next) :
    ∀ k, (next.stk k).length ≤ initialBound m word c + j * (deterministic m).pushBudget :=
  (deterministic m).run_stack_bound j ([],readyCfg m word c) ([],next)
    (initialBound m word c) (ready_bound m word c)
    (lift_run m j _ _ h)

theorem prefix_bits (word : List Bool) (c : m.Config) (j : ℕ)
    (next : (computer m).Cfg)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some (readyCfg m word c)) = some next) :
    (deterministic m).codedStorageBits next ≤ (deterministic m).controlBits +
      (initialBound m word c + j * (deterministic m).pushBudget) *
        (deterministic m).symbolWidths :=
  ((deterministic m).codedStorageBits_le next).trans
    ((deterministic m).storageBits_le next _ (prefix_capacity m word c j next h))

theorem round_primitive (token : Option Bool) (word : List Bool) (c : m.Config) :
    (deterministic m).primitiveCost 3 ([],readyCfg m (Packet.encode token ++ word) c) ≤
      3 * (deterministic m).primitiveBudget :=
  (deterministic m).primitiveCost_le 3 _

theorem round_prefix_primitive (token : Option Bool) (word : List Bool) (c : m.Config)
    (j : ℕ) (hj : j ≤ 3) :
    (deterministic m).primitiveCost j ([],readyCfg m (Packet.encode token ++ word) c) ≤
      3 * (deterministic m).primitiveBudget :=
  ((deterministic m).primitiveCost_le j _).trans
    (Nat.mul_le_mul_right (deterministic m).primitiveBudget hj)

/-- Applies to every actual successful prefix, including the two packet pops
and arbitrary primitive pushes inside the chosen original statement.
-/
theorem round_prefix_bits (token : Option Bool) (word : List Bool) (c : m.Config)
    (j : ℕ) (hj : j ≤ 3) (next : (computer m).Cfg)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some (readyCfg m (Packet.encode token ++ word) c)) = some next) :
    (deterministic m).codedStorageBits next ≤ (deterministic m).controlBits +
      (2 + word.length + sourceCells m c + 3 * (deterministic m).pushBudget) *
        (deterministic m).symbolWidths := by
  have hb := prefix_bits m (Packet.encode token ++ word) c j next h
  have hjm := Nat.mul_le_mul_right (deterministic m).pushBudget hj
  apply hb.trans
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  simp only [initialBound,List.length_append,Packet.encode_length]
  omega

theorem round_internal_tapes (token : Option Bool) (word : List Bool) (c : m.Config)
    (j : ℕ) (hj : j < 3) (next : (computer m).Cfg) (l : (computer m).Λ)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some (readyCfg m (Packet.encode token ++ word) c)) = some next) :
    PrimitiveTapeBound m ((computer m).m l) next.var next.stk
      (2 + word.length + sourceCells m c + 3 * (deterministic m).pushBudget) := by
  have hp := prefix_capacity m (Packet.encode token ++ word) c j next h
  have hs := all_primitive_tapes m ((computer m).m l) next.var next.stk _ hp
  apply primitiveTape_mono m _ _ _ _ _ hs
  have hq := instruction_pushes_le m l
  have ht := Nat.mul_le_mul_right (deterministic m).pushBudget (Nat.succ_le_of_lt hj)
  simp only [initialBound,List.length_append,Packet.encode_length,Nat.succ_mul] at *
  omega

theorem round_internal_bits (token : Option Bool) (word : List Bool) (c : m.Config)
    (j : ℕ) (hj : j < 3) (next : (computer m).Cfg) (l : (computer m).Λ)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some (readyCfg m (Packet.encode token ++ word) c)) = some next) :
    PrimitiveBitsBound m ((computer m).m l) next.var next.stk
      ((deterministic m).controlBits +
        (2 + word.length + sourceCells m c + 3 * (deterministic m).pushBudget) *
          (deterministic m).symbolWidths) :=
  tapes_to_bits m _ _ _ _ (round_internal_tapes m token word c j hj next l h)

/-- No supplied source capacity: the original input initialization itself gives
the bound used for the complete interpreter trace.
-/
theorem source_initial_bound (input : List (m.core.Γ m.core.k₀)) :
    ∀ k, ((initList m.core input).stk k).length ≤ input.length := by
  intro k
  simpa only [Function.iterate_zero_apply,Nat.zero_mul,Nat.add_zero] using
    Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound m.core input 0 k

theorem source_initial_cells (input : List (m.core.Γ m.core.k₀)) :
    sourceCells m (initList m.core input) ≤ Fintype.card m.core.K * input.length := by
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => source_initial_bound m input k)
  simpa only [sourceCells,Finset.sum_const,Finset.card_univ,smul_eq_mul] using hs

theorem packet_word_length (tokens : List (Option Bool)) :
    (tokens.flatMap Packet.encode).length = 2 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.flatMap_cons,List.length_append,Packet.encode_length,List.length_cons,ih]
    omega

def timePolynomial (T : Polynomial ℕ) : Polynomial ℕ := Polynomial.C 3 * T
def capacityPolynomial (T : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2 * T + Polynomial.C (Fintype.card m.core.K) * Polynomial.X +
    timePolynomial T * Polynomial.C (deterministic m).pushBudget
def primitivePolynomial (T : Polynomial ℕ) : Polynomial ℕ :=
  timePolynomial T * Polynomial.C (deterministic m).primitiveBudget
def bitsPolynomial (T : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (deterministic m).controlBits +
    capacityPolynomial m T * Polynomial.C (deterministic m).symbolWidths

theorem trace_primitive (T : Polynomial ℕ) (input : List (m.core.Γ m.core.k₀))
    (tokens : List (Option Bool)) (hlen : tokens.length = T.eval input.length) :
    (deterministic m).primitiveCost (3 * tokens.length)
      ([],readyCfg m (tokens.flatMap Packet.encode) (initList m.core input)) ≤
        (primitivePolynomial m T).eval input.length := by
  simpa only [primitivePolynomial,timePolynomial,Polynomial.eval_mul,Polynomial.eval_C,hlen]
    using (deterministic m).primitiveCost_le (3 * tokens.length) _

theorem trace_prefix_primitive (T : Polynomial ℕ) (input : List (m.core.Γ m.core.k₀))
    (tokens : List (Option Bool)) (hlen : tokens.length = T.eval input.length)
    (j : ℕ) (hj : j ≤ 3 * tokens.length) :
    (deterministic m).primitiveCost j
      ([],readyCfg m (tokens.flatMap Packet.encode) (initList m.core input)) ≤
        (primitivePolynomial m T).eval input.length := by
  apply ((deterministic m).primitiveCost_le j _).trans
  simpa only [primitivePolynomial,timePolynomial,Polynomial.eval_mul,Polynomial.eval_C,← hlen]
    using Nat.mul_le_mul_right (deterministic m).primitiveBudget hj

theorem trace_prefix_capacity (T : Polynomial ℕ) (input : List (m.core.Γ m.core.k₀))
    (tokens : List (Option Bool)) (hlen : tokens.length = T.eval input.length)
    (j : ℕ) (hj : j ≤ 3 * tokens.length) (next : (computer m).Cfg)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some (readyCfg m (tokens.flatMap Packet.encode) (initList m.core input))) = some next) :
    ∀ k, (next.stk k).length ≤ (capacityPolynomial m T).eval input.length := by
  intro k
  have hp := prefix_capacity m (tokens.flatMap Packet.encode) (initList m.core input) j next h k
  have hc := source_initial_cells m input
  have ht := Nat.mul_le_mul_right (deterministic m).pushBudget hj
  simp only [initialBound,packet_word_length] at hp
  apply hp.trans
  simp only [capacityPolynomial,timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,← hlen]
  omega

theorem trace_prefix_bits (T : Polynomial ℕ) (input : List (m.core.Γ m.core.k₀))
    (tokens : List (Option Bool)) (hlen : tokens.length = T.eval input.length)
    (j : ℕ) (hj : j ≤ 3 * tokens.length) (next : (computer m).Cfg)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some (readyCfg m (tokens.flatMap Packet.encode) (initList m.core input))) = some next) :
    (deterministic m).codedStorageBits next ≤ (bitsPolynomial m T).eval input.length := by
  have hc := trace_prefix_capacity m T input tokens hlen j hj next h
  simpa only [bitsPolynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul] using
    ((deterministic m).codedStorageBits_le next).trans
      ((deterministic m).storageBits_le next _ hc)

theorem trace_internal_tapes (T : Polynomial ℕ) (input : List (m.core.Γ m.core.k₀))
    (tokens : List (Option Bool)) (hlen : tokens.length = T.eval input.length)
    (j : ℕ) (hj : j < 3 * tokens.length) (next : (computer m).Cfg) (l : (computer m).Λ)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some (readyCfg m (tokens.flatMap Packet.encode) (initList m.core input))) = some next) :
    PrimitiveTapeBound m ((computer m).m l) next.var next.stk
      ((capacityPolynomial m T).eval input.length) := by
  have hp := prefix_capacity m (tokens.flatMap Packet.encode) (initList m.core input) j next h
  have hs := all_primitive_tapes m ((computer m).m l) next.var next.stk _ hp
  apply primitiveTape_mono m _ _ _ _ _ hs
  have hc := source_initial_cells m input
  have hq := instruction_pushes_le m l
  have ht := Nat.mul_le_mul_right (deterministic m).pushBudget (Nat.succ_le_of_lt hj)
  change (j+1) * (deterministic m).pushBudget ≤ (3 * tokens.length) * (deterministic m).pushBudget at ht
  rw [Nat.add_mul, Nat.one_mul] at ht
  simp only [initialBound,packet_word_length] at *
  simp only [capacityPolynomial,timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,← hlen]
  omega

theorem trace_internal_bits (T : Polynomial ℕ) (input : List (m.core.Γ m.core.k₀))
    (tokens : List (Option Bool)) (hlen : tokens.length = T.eval input.length)
    (j : ℕ) (hj : j < 3 * tokens.length) (next : (computer m).Cfg) (l : (computer m).Λ)
    (h : (fun p : Option (computer m).Cfg => p.bind (computer m).step)^[j]
      (some (readyCfg m (tokens.flatMap Packet.encode) (initList m.core input))) = some next) :
    PrimitiveBitsBound m ((computer m).m l) next.var next.stk
      ((bitsPolynomial m T).eval input.length) := by
  simpa only [bitsPolynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul] using
    tapes_to_bits m _ _ _ _ (trace_internal_tapes m T input tokens hlen j hj next l h)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Program
