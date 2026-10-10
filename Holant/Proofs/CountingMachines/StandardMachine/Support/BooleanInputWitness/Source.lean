import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Standard
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Sole entry for the arbitrary
finite-alphabet Boolean-input witness bridge. The original SharpPWitness alone
produces fixed-block input, physical original P(N), suffix guard, old-prefix
reconstruction, old verifier and strict result decoder. The old generic tagged
parser supplies the actual SharpPWitness input/output stream interface. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Source
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}
variable (w : SharpPWitness ea f)

def firstBits (a : α) (b : Fin (newLength w a) → Bool) : List Bool :=
  (List.ofFn b).take (oldLength w a)
def tail (a : α) (b : Fin (newLength w a) → Bool) : List Bool :=
  (List.ofFn b).drop (oldLength w a)

theorem candidate_length (a : α) (b : Fin (newLength w a) → Bool) :
    oldLength w a ≤ (List.ofFn b).length := by
  simpa only [List.length_ofFn] using oldLength_le_newLength w a

theorem guarded_value (a : α) (b : Fin (newLength w a) → Bool) :
    paddedAccept w (a,List.ofFn b) =
      (Guard.check (firstBits w a b,tail w a b)).elim false
        (fun bits => w.accept (a,bits)) := by
  simp only [paddedAccept,Padding.accept,Padding.extract,firstBits,tail,Guard.check,
    if_pos (candidate_length w a b)]

/-- The physical guard input contains the internally determined old P(N)
counter and ALL actual new witness bits, in the original order. -/
theorem guard_word (a : α) (b : Fin (newLength w a) → Bool) :
    Guard.inputEncoding.encode (firstBits w a b,tail w a b) =
      List.replicate (oldLength w a) true ++ false::List.ofFn b := by
  simp only [Guard.inputEncoding,firstBits,tail,List.length_take,
    Nat.min_eq_left (candidate_length w a b),List.take_append_drop]

def guard_outputs (a : α) (b : Fin (newLength w a) → Bool) :
    TM2OutputsInTime Guard.machine.computer
      (List.replicate (oldLength w a) true ++ false::List.ofFn b)
      (some (Guard.outputEncoding.encode (Guard.check (firstBits w a b,tail w a b))))
      (Guard.computes.time.eval
        (List.replicate (oldLength w a) true ++ false::List.ofFn b).length) := by
  have h := Guard.computes.outputs (firstBits w a b,tail w a b)
  simp only [guard_word] at h
  exact h

def verifier_outputs (a : α) (b : Fin (newLength w a) → Bool) :
    TM2OutputsInTime (compiledMachine w).computer
      ((pairEncoding w).encode (a,firstBits w a b))
      (some ((outputEncoding w).encode (w.accept (a,firstBits w a b))))
      (w.verifier.time.eval ((pairEncoding w).encode (a,firstBits w a b)).length) :=
  (compiledComputes w).outputs (a,firstBits w a b)

/-- Component receipts derive every candidate transport and the exact same-f
count from the original witness. The full public constructor appears below. -/
theorem components :
    (∀ a, ((inputEncoding w).encode a).length = codeWidth w*(ea.encode a).length) ∧
    (∀ a, f a = witnessCount (newLength w a) (fun bits => paddedAccept w (a,bits))) ∧
    Nonempty (Computes (pairEncoding w) (outputEncoding w) w.accept) ∧
    Nonempty (Computes Guard.inputEncoding Guard.outputEncoding Guard.check) ∧
    (∀ a (b : Fin (newLength w a) → Bool),
      paddedAccept w (a,List.ofFn b) =
        (Guard.check (firstBits w a b,tail w a b)).elim false
          (fun bits => w.accept (a,bits))) :=
  ⟨input_length w,padded_counts w,⟨compiledComputes w⟩,⟨Guard.computes⟩,guarded_value w⟩

/-- Unique public constructor. No counter, padding law, simulator, decoded
candidate, verifier answer or model-equivalence premise is accepted. -/
def source : SharpPWitness (inputEncoding w) f := Standard.witness w

/-- The actual accepted old witnesses biject the actual accepted padded
witnesses by prefix recovery and the uniquely false suffix. -/
def acceptedWitnessEquiv (a : α) :
    {bits : Fin (oldLength w a) → Bool // w.accept (a,List.ofFn bits) = true} ≃
      {bits : Fin (newLength w a) → Bool // paddedAccept w (a,List.ofFn bits) = true} :=
  Padding.acceptedEquivOfLe (oldLength w a) (newLength w a)
    (oldLength_le_newLength w a) (fun bits => w.accept (a,bits))

/-- Explicit end-to-end accepted-vector/path maps for the original arbitrary
finite-alphabet witness. Every original bit is recovered; added bits are forced
false and every deterministic/held-halt edge has its canonical token. -/
def acceptedPhysicalEquiv (a : α) :
    {bits : Fin (oldLength w a) → Bool // w.accept (a,List.ofFn bits) = true} ≃
      BooleanOpcode.Source.NativePhysicalPath (source w) a :=
  (acceptedWitnessEquiv w a).trans (BooleanOpcode.Source.native_accepted_equiv (source w) a)

theorem same_f (a : α) :
    f a = witnessCount ((source w).witnessLength.eval ((inputEncoding w).encode a).length)
      (fun bits => (source w).accept (a,bits)) := (source w).counts a

theorem inSharpP : InSharpP (inputEncoding w) f := ⟨source w⟩

def original_counter_outputs (a : α) :
    TM2OutputsInTime (Counter.oldWitnessComputes w).machine.computer
      ((inputEncoding w).encode a)
      (some (List.replicate (oldLength w a) true))
      ((Counter.oldWitnessComputes w).time.eval ((inputEncoding w).encode a).length) :=
  (Counter.oldWitnessComputes w).outputs a

def frontend_outputs (p : α × List Bool) :
    TM2OutputsInTime (Frontend.computes w).machine.computer
      ((Frontend.dataEncoding w).encode p)
      (some (encodingBoolBool.encode (paddedAccept w p)))
      ((Frontend.computes w).time.eval ((Frontend.dataEncoding w).encode p).length) :=
  (Frontend.computes w).outputs p

/-- Actual primitive instruction cost of the generated frontend, including
fanout, framing, two-pass transfers, polynomial counter and BOTH guard runs. -/
theorem frontend_primitive (p : α × List Bool) :
    primitiveCost (Frontend.computes w).machine ((Frontend.computes w).outputs p).steps
      (some (initList (Frontend.computes w).machine.computer ((Frontend.dataEncoding w).encode p))) ≤
      (primitivePolynomial (Frontend.computes w)).eval ((Frontend.dataEncoding w).encode p).length :=
  computes_primitive_cost (Frontend.computes w) p

def inputWord (p : α × List Bool) : List (Bool ⊕ Bool) :=
  (encodingProd (inputEncoding w) (encodingList Bool)).encode p

def standard_outputs (p : α × List Bool) :
    TM2OutputsInTime (Standard.verifier w).tm (inputWord w p)
      (some [Sum.inr (paddedAccept w p)]) ((Standard.time w).eval (inputWord w p).length) := by
  have h := (Standard.verifier w).outputsFun p
  change TM2OutputsInTime (Standard.verifier w).tm (List.map id (inputWord w p))
    (some (List.map id [Sum.inr (paddedAccept w p)]))
    ((Standard.time w).eval (inputWord w p).length) at h
  simpa only [List.map_id] using h

theorem deterministic_advance (log : List Bool) (c : (original (source w)).Config) :
    (original (source w)).advance (log,c) =
      some (log,Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (Standard.verifier w).tm c) := by
  cases hl : c.l <;>
    simp [BinaryMachine.advance,BinaryMachine.step,original,Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep,hl,source,
      Standard.witness]

theorem held_run (t : ℕ) (log : List Bool) (c : (original (source w)).Config) :
    (original (source w)).run t (log,c) =
      some (log,(Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (Standard.verifier w).tm)^[t] c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      rw [BinaryMachine.run,deterministic_advance,Option.bind_some,ih,
        Function.iterate_succ_apply]

/-- Full advertised clock is produced from the successful physical run;
halt padding uses the sole unchanged deterministic edge. -/
theorem run_at_bound (p : α × List Bool) (log : List Bool) :
    (original (source w)).run ((Standard.time w).eval (inputWord w p).length)
      (log,initList (Standard.verifier w).tm (inputWord w p)) =
      some (log,haltList (Standard.verifier w).tm [Sum.inr (paddedAccept w p)]) := by
  rw [held_run,Holant.LocalDrafts.CountingHardness.VerifierRun.outputs_at_bound _ _ _ _ (standard_outputs w p)]

/-- Finite heterogeneous primitive accounting on the SAME standard machine.
No endpoint or successful clock supplied by the caller. -/
theorem standard_primitive (p : α × List Bool) (log : List Bool) :
    (original (source w)).primitiveCost ((Standard.time w).eval (inputWord w p).length)
      (log,initList (Standard.verifier w).tm (inputWord w p)) ≤
      ((Standard.time w)*Polynomial.C (original (source w)).primitiveBudget).eval
        (inputWord w p).length := by
  simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
    (original (source w)).primitiveCost_le ((Standard.time w).eval (inputWord w p).length)
      (log,initList (Standard.verifier w).tm (inputWord w p))

/-- All actual clock-prefix stacks, including parsing and every old work
stack, are bounded by original syntactic push counts of the generated machine. -/
theorem standard_storage (p : α × List Bool) (t : ℕ)
    (ht : t ≤ (Standard.time w).eval (inputWord w p).length)
    (k : (Standard.verifier w).tm.K) :
    (((Holant.LocalDrafts.CountingHardness.VerifierRun.holdStep (Standard.verifier w).tm)^[t]
      (initList (Standard.verifier w).tm (inputWord w p))).stk k).length ≤
      (Polynomial.X+(Standard.time w)*Polynomial.C
        (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (Standard.verifier w).tm)).eval (inputWord w p).length := by
  have h := Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound (Standard.verifier w).tm (inputWord w p) t k
  exact h.trans (by
    simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right
        (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (Standard.verifier w).tm) ht) (inputWord w p).length)

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Source
