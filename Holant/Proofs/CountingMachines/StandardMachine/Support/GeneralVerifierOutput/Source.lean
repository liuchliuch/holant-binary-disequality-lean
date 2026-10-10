import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralVerifierOutput.Tagged

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Sole entry for arbitrary original finite-alphabet
SharpPWitness output normalization. Every operational producer is constructed
from w: old real verifier -> literal Boolean opcode compiler -> strict old
singleton block reader/EOF/eraser -> actual four-symbol tagged output stack.
This entry does not adapt the standard tagged input/witness framing, choose a
new witness length, or identify any conventional #P machine model. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralVerifierOutput.Source
open Turing Computability Holant.Complexity BinaryCompose
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}
variable (w : SharpPWitness ea f)

/-- The middle word is the OLD actual output symbol's code, with its original
alphabet enumeration. Its length is derived internally, never supplied. -/
def resultBound : PolynomialOutputBound (BooleanInputWitness.pairEncoding w)
    (BooleanInputWitness.outputEncoding w) w.accept where
  bound := Polynomial.C (BooleanOpcode.Code.width (BooleanInputWitness.original w)
    w.verifier.tm.k₁)
  length_le p := by
    simp [BooleanInputWitness.outputEncoding,BooleanOpcode.Code.symbol_length,BooleanInputWitness.original]

/-- The requested plain Bool interface, backed by the actual disjoint-stack
composition programme. No caller decoder-success/Computes premise is needed. -/
def computes : Computes (BooleanInputWitness.pairEncoding w) encodingBoolBool w.accept :=
  (BooleanInputWitness.compiledComputes w).comp (Decoder.computes w) (resultBound w)

/-- Generic standard output adapter for an internally produced plain Bool
machine. In particular BinaryInputWitness may feed its own physical frontend;
this constructor executes and proves the heterogeneous wrapper's real table. -/
def taggedComputes {A : Type} {e : Encoding A Bool} {g : A → Bool}
    (c : Computes e encodingBoolBool g) : PolyTime e (taggedBoolEncoding Bool) g :=
  Tagged.taggedComputes c

/-- Arbitrary original Γ is retained. Only output normalization is performed;
the whole-pair input is the exact old verifier's fixed-block serialization. -/
def standardVerifier : PolyTime (BooleanInputWitness.pairEncoding w)
    (taggedBoolEncoding Bool) w.accept := taggedComputes (computes w)

abbrev machine := Tagged.machine (computes w).machine
def timePolynomial : Polynomial ℕ := (computes w).time+1
def time (p : α × List Bool) : ℕ :=
  (timePolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length

theorem plain_time : (computes w).time = w.verifier.time +
    Polynomial.C (2*(BooleanOpcode.Code.width (BooleanInputWitness.original w)
      w.verifier.tm.k₁+1)+3) := by
  simp [computes,Computes.comp,BooleanInputWitness.compiledComputes,resultBound,
    Decoder.computes] <;> ring

theorem standard_time : timePolynomial w = w.verifier.time +
    Polynomial.C (2*(BooleanOpcode.Code.width (BooleanInputWitness.original w)
      w.verifier.tm.k₁+1)+4) := by
  rw [timePolynomial,plain_time]
  have hc : Polynomial.C (2*(BooleanOpcode.Code.width (BooleanInputWitness.original w)
      w.verifier.tm.k₁+1)+4) =
      Polynomial.C (2*(BooleanOpcode.Code.width (BooleanInputWitness.original w)
        w.verifier.tm.k₁+1)+3)+1 := by
    rw [show 2*(BooleanOpcode.Code.width (BooleanInputWitness.original w)
        w.verifier.tm.k₁+1)+4 =
        (2*(BooleanOpcode.Code.width (BooleanInputWitness.original w)
          w.verifier.tm.k₁+1)+3)+1 by omega,Polynomial.C_add]
    rfl
  rw [hc,add_assoc]

/-- Actual original source input/output aliases are preserved by the opcode
compiler; neither this producer nor the decoder requires their distinction. -/
theorem compiled_alias (h : w.verifier.tm.k₀ = w.verifier.tm.k₁) :
    (BooleanInputWitness.compiledComputes w).machine.input =
      (BooleanInputWitness.compiledComputes w).machine.output := h

theorem original_statement (label : w.verifier.tm.Λ) :
    (BooleanInputWitness.compiledComputes w).machine.program label =
      BooleanOpcode.Compiler.statement (BooleanInputWitness.original w)
        (w.verifier.tm.m label) := rfl

@[simp] theorem input_key : (machine w).core.k₀ =
    Sum.inr (Sum.inl w.verifier.tm.k₀) := rfl
@[simp] theorem output_key : (machine w).core.k₁ = Sum.inl () := rfl

theorem original_alias_in_whole_machine (h : w.verifier.tm.k₀ = w.verifier.tm.k₁) :
    (Sum.inr (Sum.inl w.verifier.tm.k₀) : (machine w).core.K) =
      Sum.inr (Sum.inl w.verifier.tm.k₁) :=
  congrArg (fun key : w.verifier.tm.K =>
    (Sum.inr (Sum.inl key) : (machine w).core.K)) h

theorem input_length (p : α × List Bool) :
    ((BooleanInputWitness.pairEncoding w).encode p).length =
      BooleanInputWitness.codeWidth w * ((ea.encode p.1).length+p.2.length) :=
  BooleanInputWitness.pair_length w p

@[simp] theorem standard_input_word (p : α × List Bool) :
    ((BooleanInputWitness.pairEncoding w).encode p).map
      (standardVerifier w).inputAlphabet.symm =
        (BooleanInputWitness.pairEncoding w).encode p := List.map_id _

@[simp] theorem standard_output_word (b : Bool) :
    ((taggedBoolEncoding Bool).encode b).map (standardVerifier w).outputAlphabet.symm =
      [Sum.inr b] := rfl

/-- Whole ordinary TM2 computation, with the standard four-symbol output
alphabet and the exact old pair's original block-coded input. -/
def outputs (p : α × List Bool) :
    TM2OutputsInTime (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)
      (some [Sum.inr (w.accept p)]) (time w p) := by
  have ho := (standardVerifier w).outputsFun p
  change TM2OutputsInTime (machine w).core
    (List.map id ((BooleanInputWitness.pairEncoding w).encode p))
    (some (List.map id [Sum.inr (w.accept p)])) (time w p) at ho
  rw [List.map_id,List.map_id] at ho
  exact ho

theorem run_at_bound (p : α × List Bool) (log : List Bool) :
    (machine w).run (time w p)
      (log,initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) =
        some (log,haltList (machine w).core [Sum.inr (w.accept p)]) :=
  Tagged.run_at_bound (computes w) p log

theorem halt_value_injective : Function.Injective (fun b : Bool =>
    haltList (machine w).core [Sum.inr b]) := by
  intro a b h
  have hs := congrArg (fun c : (machine w).Config => c.stk (machine w).core.k₁) h
  change ([Sum.inr a] : List (Bool ⊕ Bool)) = [Sum.inr b] at hs
  exact Sum.inr.inj (List.cons.inj hs).1

theorem accepts_iff (p : α × List Bool) :
    (machine w).run (time w p)
      ([],initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) =
        some ([],haltList (machine w).core [Sum.inr true]) ↔ w.accept p = true := by
  rw [run_at_bound]
  constructor
  · intro h
    exact halt_value_injective w (congrArg Prod.snd (Option.some.inj h))
  · intro h
    rw [h]

theorem canonical_trace (p : α × List Bool) :
    (machine w).TraceValid (List.replicate (time w p) none)
      (initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p))
      (haltList (machine w).core [Sum.inr (w.accept p)]) := by
  obtain ⟨bits,hlen,hlog,ht⟩ := (machine w).run_trace _ _ _ (run_at_bound w p [])
  rw [Tagged.trace_tokens_none (computes w).machine bits _ _ ht,hlen] at ht
  exact ht

theorem trace_tokens_unique (p : α × List Bool) (bits : List (Option Bool))
    (hlen : bits.length = time w p) (c : (machine w).Config)
    (h : (machine w).TraceValid bits
      (initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) c) :
    bits = List.replicate (time w p) none := by
  rw [Tagged.trace_tokens_none (computes w).machine bits _ _ h,hlen]

def capacityPolynomial : Polynomial ℕ := Polynomial.X+
  timePolynomial w * Polynomial.C (machine w).pushBudget
def primitivePolynomial : Polynomial ℕ :=
  timePolynomial w * Polynomial.C (machine w).primitiveBudget
def bitsPolynomial : Polynomial ℕ := Polynomial.C (machine w).controlBits+
  capacityPolynomial w * Polynomial.C (machine w).symbolWidths
def internalCapacityPolynomial : Polynomial ℕ :=
  capacityPolynomial w + Polynomial.C (machine w).primitiveBudget
def internalBitsPolynomial : Polynomial ℕ := Polynomial.C (machine w).controlBits+
  internalCapacityPolynomial w * Polynomial.C (machine w).symbolWidths

/-- Initial capacity is the literal original pair serialization's bit length. -/
theorem initial_capacity (p : α × List Bool) : ∀ key,
    ((initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)).stk key).length ≤
      ((BooleanInputWitness.pairEncoding w).encode p).length := by
  intro key
  by_cases hk : key = (machine w).core.k₀
  · subst key
    simp [initList]
  · simp [initList,hk]

theorem prefix_capacity (p : α × List Bool) (j : ℕ) (log : List Bool)
    (next : List Bool × (machine w).Config) (hj : j ≤ time w p)
    (hr : (machine w).run j
      (log,initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) = some next) :
    ∀ key, (next.2.stk key).length ≤
      (capacityPolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length := by
  have hs := (machine w).run_stack_bound j _ _
    ((BooleanInputWitness.pairEncoding w).encode p).length (initial_capacity w p) hr
  intro key
  exact (hs key).trans (by
    simpa [capacityPolynomial,time] using Nat.add_le_add_left
      (Nat.mul_le_mul_right (machine w).pushBudget hj)
      ((BooleanInputWitness.pairEncoding w).encode p).length)

theorem prefix_primitive (p : α × List Bool) (j : ℕ) (log : List Bool)
    (hj : j ≤ time w p) :
    (machine w).primitiveCost j
      (log,initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) ≤
        (primitivePolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length := by
  exact ((machine w).primitiveCost_le j _).trans (by
    simpa [primitivePolynomial,time] using Nat.mul_le_mul_right (machine w).primitiveBudget hj)

theorem prefix_bits (p : α × List Bool) (j : ℕ) (log : List Bool)
    (next : List Bool × (machine w).Config) (hj : j ≤ time w p)
    (hr : (machine w).run j
      (log,initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) = some next) :
    (machine w).codedStorageBits next.2 ≤
      (bitsPolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length := by
  apply ((machine w).codedStorageBits_le next.2).trans
  simpa [bitsPolynomial] using (machine w).storageBits_le next.2 _
    (prefix_capacity w p j log next hj hr)

/-- No prefix trajectory/capacity premise is needed: the same actual complete
run internally supplies every finite prefix and all of its physical bounds. -/
theorem actual_prefix (p : α × List Bool) (j : ℕ) (hj : j ≤ time w p) :
    ∃ next : (machine w).Config,
      (machine w).run j
        ([],initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) = some ([],next) ∧
      (∀ key, (next.stk key).length ≤
        (capacityPolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length) ∧
      (machine w).primitiveCost j
        ([],initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) ≤
          (primitivePolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length ∧
      (machine w).codedStorageBits next ≤
        (bitsPolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length := by
  let next := (Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (machine w).core)^[j]
    (initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p))
  have hr : (machine w).run j
      ([],initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) = some ([],next) :=
    Tagged.run_eq_hold (computes w).machine j [] _
  exact ⟨next,hr,prefix_capacity w p j [] ([],next) hj hr,
    prefix_primitive w p j [] hj,prefix_bits w p j [] ([],next) hj hr⟩

/-- Every literal statement's complete primitive derivation is constructed
from its actual syntax/execute result, not supplied as a verifier law. -/
theorem statement_prefix (label : (machine w).core.Λ)
    (v : (machine w).core.σ) (S : ∀ key, List ((machine w).core.Γ key)) :
    BooleanOpcode.NativeExecution.PrimitivePrefix ((machine w).core.m label) v S
      (HeterogeneousCost.execute ((machine w).core.m label) v S).1
      (TM2.stepAux ((machine w).core.m label) v S).var
      (TM2.stepAux ((machine w).core.m label) v S).stk :=
  BooleanOpcode.NativeExecution.primitive_full _ _ _

/-- Temporary states inside the same finite instruction table are charged too.
hr/h describe the observed actual prefix, not a free Computes/simulation law. -/
theorem internal_prefix (p : α × List Bool) (j : ℕ)
    (next : List Bool × (machine w).Config) (hj : j < time w p)
    (hr : (machine w).run j
      ([],initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p)) = some next)
    (label : (machine w).core.Λ) (hl : next.2.l = some label)
    (n : ℕ) (v : (machine w).core.σ) (S : ∀ key, List ((machine w).core.Γ key))
    (h : BooleanOpcode.NativeExecution.PrimitivePrefix ((machine w).core.m label)
      next.2.var next.2.stk n v S) (control : Option (machine w).core.Λ) :
    (machine w).primitiveCost j
      ([],initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p))+(n+1) ≤
        (primitivePolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length ∧
    (machine w).codedStorageBits ⟨control,v,S⟩ ≤
      (internalBitsPolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length := by
  have hb : n+1 ≤ (machine w).primitiveBudget :=
    (Nat.add_le_add_right (BooleanOpcode.NativeExecution.primitive_prefix_cost _ _ _ _ _ _ h) 1).trans
      ((machine w).core_budget_le label)
  constructor
  · have hc := (machine w).primitiveCost_le j
      ([],initList (machine w).core ((BooleanInputWitness.pairEncoding w).encode p))
    have ht := Nat.mul_le_mul_right (machine w).primitiveBudget (Nat.succ_le_of_lt hj)
    have he := Nat.add_le_add hc hb
    simp only [Nat.succ_mul] at ht
    exact he.trans (by simpa [primitivePolynomial,time] using ht)
  · have hs := prefix_capacity w p j [] next (Nat.le_of_lt hj) hr
    have hu := BooleanOpcode.NativeExecution.primitive_prefix_capacity _ _ _ _ _ _ h _ hs
    have hS : ∀ key, (S key).length ≤
        (internalCapacityPolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length := by
      intro key
      exact (hu key).trans (by
        simpa [internalCapacityPolynomial] using Nat.add_le_add_left
          ((Nat.le_add_right n 1).trans hb)
          ((capacityPolynomial w).eval ((BooleanInputWitness.pairEncoding w).encode p).length))
    exact ((machine w).codedStorageBits_le _).trans (by
      simpa [internalBitsPolynomial] using (machine w).storageBits_le ⟨control,v,S⟩ _ hS)
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralVerifierOutput.Source
