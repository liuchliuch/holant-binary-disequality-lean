import Holant.Proofs.CountingMachines.StandardMachine.Support.Execution
import Holant.Proofs.CountingMachines.StandardMachine.Support.Cost
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option backward.isDefEq.respectTransparency false
/-!
Locally checked adaptation of the frozen reference proof. Sole forward presentation entry.
Every supplied object is the original SharpPWitness. The presentation computes
its unary witness length from original input bytes, chooses exactly that many
bits and runs the same actual verifier. Accepted paths are defined by the real
finite-program run, not by a predicate definitionally equal to SharpP.

This is a forward bridge into this explicit binary finite-TM2 presentation.
An arbitrary nondeterministic presentation -> SharpPWitness conversion, and its
identification with a separately chosen conventional #P model, are NOT asserted.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source
open Turing Computability Holant.Complexity BinaryCompose
open WitnessMachine
open scoped BigOperators
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

abbrev machine : BinaryMachine := WitnessMachine.machine w

def timePolynomial : Polynomial ℕ := (prepareComputes w).time +
  Polynomial.C 2 * Polynomial.X + Polynomial.C 2 * w.witnessLength +
    Polynomial.C 4 + Holant.LocalDrafts.CountingHardness.VerifierRun.horizonPolynomial w

def time (a : α) : ℕ := (timePolynomial w).eval (ea.encode a).length

theorem execution_le_time (a : α) : executionSteps w a ≤ time w a := by
  have hp := ((prepareComputes w).outputs a).steps_le_m
  simpa [executionSteps,time,timePolynomial,Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength,
    Holant.LocalDrafts.CountingHardness.VerifierRun.horizon,Nat.add_assoc] using Nat.add_le_add_right hp
      (2 * (ea.encode a).length + 2 * Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a + 4 + Holant.LocalDrafts.CountingHardness.VerifierRun.horizon w a)

theorem padded_run (a : α) (choices rest : List Bool)
    (hlen : choices.length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) :
    (machine w).run (time w a)
      (choices ++ rest,initList (computer w) (ea.encode a)) =
      some (rest,terminal w (w.accept (a,choices.reverse))) := by
  have ht := execution_le_time w a
  rw [show time w a = (time w a - executionSteps w a) + executionSteps w a by omega,
    BinaryMachine.run_add]
  rw [full_run w a choices rest hlen,Option.bind_some]
  exact BinaryMachine.run_halt _ _ _ _ rfl

theorem padded_run_clean (a : α) (choices rest : List Bool)
    (hlen : choices.length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) :
    (machine w).run (time w a)
      (choices ++ rest,initList (computer w) (ea.encode a)) =
      some (rest,haltList (computer w) [w.verifier.outputAlphabet.symm
        (Sum.inr (w.accept (a,choices.reverse)))]) := by
  rw [padded_run w a choices rest hlen,terminal_eq_halt]

/-- Too short a branch log fails at the actual split label; no accepting
completion or free padding bit is supplied to fill it. -/
theorem short_log_fails (a : α) (choices : List Bool)
    (hlen : choices.length < Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) :
    (machine w).run (time w a) (choices,initList (computer w) (ea.encode a)) = none := by
  let cutoff := ((prepareComputes w).outputs a).steps + (ea.encode a).length + 1 +
    (2 * Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a + 1)
  have hcut : cutoff ≤ time w a := by
    have hp := ((prepareComputes w).outputs a).steps_le_m
    dsimp [cutoff,time,timePolynomial,Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  have hbad : (machine w).run cutoff (choices,initList (computer w) (ea.encode a)) = none := by
    have he : cutoff = (2 * Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a + 1) +
      ((ea.encode a).length + 1 + ((prepareComputes w).outputs a).steps) := by dsimp [cutoff]; omega
    rw [he,BinaryMachine.run_add,BinaryMachine.run_add,preparation_run,Option.bind_some,
      scan_run,Option.bind_some]
    simp only [List.append_nil]
    exact choice_short w _ choices _ [] hlen
  rw [show time w a = (time w a - cutoff) + cutoff by omega,BinaryMachine.run_add,hbad]
  rfl

theorem terminal_injective : Function.Injective (terminal w) := by
  intro b d h
  have ho := congrArg (fun c : (machine w).Config => c.stk (.inr w.verifier.tm.k₁)) h
  have hs : [w.verifier.outputAlphabet.symm (Sum.inr b)] =
      [w.verifier.outputAlphabet.symm (Sum.inr d)] := by
    simpa [terminal,verifierCfg,SumStacks.rightCfg,SumStacks.merge,haltList] using ho
  have hb := w.verifier.outputAlphabet.symm.injective (List.singleton_inj.mp hs)
  exact Sum.inr.inj hb

/-- Acceptance of a computation requires all and only its actual split bits to
be consumed. The terminal is the actual verifier's clean true output. -/
def Accepts (a : α) (choices : List Bool) : Prop :=
  (machine w).run (time w a) (choices,initList (computer w) (ea.encode a)) =
    some ([],terminal w true)

theorem accepts_iff (a : α) (choices : List Bool) :
    Accepts w a choices ↔ choices.length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a ∧
      w.accept (a,choices.reverse) = true := by
  constructor
  · intro h
    have hge : Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a ≤ choices.length := by
      by_contra hn
      have hs := short_log_fails w a choices (by omega)
      unfold Accepts at h
      rw [hs] at h
      cases h
    let first := choices.take (Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a)
    let rest := choices.drop (Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a)
    have hfirst : first.length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a := by
      simp only [first,List.length_take,Nat.min_eq_left hge]
    have he : first ++ rest = choices := List.take_append_drop _ _
    have hr := padded_run w a first rest hfirst
    rw [he] at hr
    have hout : (rest,terminal w (w.accept (a,first.reverse))) = ([],terminal w true) :=
      Option.some.inj (hr.symm.trans h)
    have hrest : rest = [] := congrArg Prod.fst hout
    have hlength : choices.length = Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a := by
      have hz := congrArg List.length hrest
      simp only [rest,List.length_drop,List.length_nil] at hz
      omega
    have hfirsteq : first = choices := by simp only [first,← hlength,List.take_length]
    have hb := terminal_injective w (congrArg Prod.snd hout)
    rw [hfirsteq] at hb
    exact ⟨hlength,hb⟩
  · rintro ⟨hlen,hb⟩
    have hr := padded_run w a choices [] hlen
    simp only [List.append_nil,hb] at hr
    exact hr

abbrev AcceptedPath (a : α) := {choices : List Bool // Accepts w a choices}
abbrev AcceptedWitness (a : α) :=
  {bits : Fin (Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) → Bool // w.accept (a,List.ofFn bits) = true}

def decodeBits (a : α) (p : AcceptedPath w a) : Fin (Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) → Bool :=
  fun i => p.val.reverse.get ⟨i.val,by
    have h := ((accepts_iff w a p.val).mp p.property).1
    rw [List.length_reverse,h]
    exact i.isLt⟩

theorem decodeBits_word (a : α) (p : AcceptedPath w a) :
    List.ofFn (decodeBits w a p) = p.val.reverse := by
  apply List.ext_getElem
  · rw [List.length_ofFn,List.length_reverse]
    exact ((accepts_iff w a p.val).mp p.property).1.symm
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

/-- Explicit two-way unique bijection. The reversal records the chronological
push order of genuine machine choices, rather than adding unused branch bits. -/
def acceptedPathEquiv (a : α) : AcceptedWitness w a ≃ AcceptedPath w a where
  toFun p := ⟨(List.ofFn p.val).reverse,(accepts_iff w a _).mpr ⟨by
    rw [List.length_reverse,List.length_ofFn],by simpa only [List.reverse_reverse] using p.property⟩⟩
  invFun p := ⟨decodeBits w a p,by
    rw [decodeBits_word]
    exact ((accepts_iff w a p.val).mp p.property).2⟩
  left_inv p := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [decodeBits_word]
    exact List.reverse_reverse _
  right_inv p := by
    apply Subtype.ext
    change (List.ofFn (decodeBits w a p)).reverse = p.val
    rw [decodeBits_word,List.reverse_reverse]

noncomputable instance acceptedPathFintype (a : α) : Fintype (AcceptedPath w a) :=
  Fintype.ofEquiv (AcceptedWitness w a) (acceptedPathEquiv w a)

def pathCount (a : α) : ℕ := Fintype.card (AcceptedPath w a)

theorem accepted_witness_card (a : α) :
    Fintype.card (AcceptedWitness w a) =
      countAccepted (fun bits : Fin (Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) → Bool =>
        w.accept (a,List.ofFn bits)) := by
  classical
  rw [Fintype.card_subtype,Finset.card_filter]
  unfold countAccepted
  apply Finset.sum_congr rfl
  intro bits _
  cases h : w.accept (a,List.ofFn bits) <;> simp [h]

/-- Count equality follows from the actual execution theorem and bijection. -/
theorem path_count (a : α) : pathCount w a = f a := by
  calc
    pathCount w a = Fintype.card (AcceptedWitness w a) :=
      Fintype.card_congr (acceptedPathEquiv w a).symm
    _ = countAccepted (fun bits : Fin (Holant.LocalDrafts.CountingHardness.VerifierRun.witnessLength w a) → Bool =>
      w.accept (a,List.ofFn bits)) := accepted_witness_card w a
    _ = f a := (w.counts a).symm

def pathRows (a : α) (p : AcceptedPath w a) :
    Fin (time w a + 1) → List Bool × (machine w).Config := fun i =>
  Classical.choose ((machine w).prefix_exists (time w a) i.val
    (p.val,initList (computer w) (ea.encode a)) ([],terminal w true)
      p.property (by omega))

theorem pathRows_run (a : α) (p : AcceptedPath w a) (i : Fin (time w a + 1)) :
    (machine w).run i.val (p.val,initList (computer w) (ea.encode a)) =
      some (pathRows w a p i) := Classical.choose_spec
    ((machine w).prefix_exists (time w a) i.val
      (p.val,initList (computer w) (ea.encode a)) ([],terminal w true) p.property (by omega))

theorem pathRows_last (a : α) (p : AcceptedPath w a) :
    pathRows w a p (Fin.last (time w a)) = ([],terminal w true) :=
  Option.some.inj ((pathRows_run w a p (Fin.last (time w a))).symm.trans p.property)

theorem pathRows_valid (a : α) (p : AcceptedPath w a) :
    (machine w).IsLogTrajectory (p.val,initList (computer w) (ea.encode a))
      (time w a) (pathRows w a p) := by
  constructor
  · exact (Option.some.inj (pathRows_run w a p 0)).symm
  · intro i
    have hs := pathRows_run w a p i.succ
    change (machine w).run (i.val + 1) _ = some _ at hs
    have hi := pathRows_run w a p i.castSucc
    simp only [Fin.val_castSucc] at hi
    rw [show i.val + 1 = 1 + i.val by omega,BinaryMachine.run_add,
      hi,Option.bind_some,BinaryMachine.run_one] at hs
    exact hs

theorem pathRows_unique (a : α) (p : AcceptedPath w a)
    (rows : Fin (time w a + 1) → List Bool × (machine w).Config)
    (h : (machine w).IsLogTrajectory (p.val,initList (computer w) (ea.encode a))
      (time w a) rows) : rows = pathRows w a p :=
  (machine w).trajectory_unique _ _ rows _ h (pathRows_valid w a p)

/-- Erasing the path observer gives genuine binary TM2 edges on actual machine
configurations. It does not install a branch log as runtime input memory. -/
theorem physical_trajectory (a : α) (p : AcceptedPath w a) :
    (machine w).IsTrajectory (initList (computer w) (ea.encode a)) (time w a)
      (fun i => (machine w).token (pathRows w a p i.castSucc))
      (fun i => (pathRows w a p i).2) :=
  (machine w).erase_log_trajectory _ _ _ (pathRows_valid w a p)

def capacityPolynomial : Polynomial ℕ := Polynomial.X +
  timePolynomial w * Polynomial.C (machine w).pushBudget

/-- Bound at every actual prefix, with the original encoded input length. -/
theorem pathRows_capacity (a : α) (p : AcceptedPath w a)
    (i : Fin (time w a + 1)) (k : (machine w).core.K) :
    ((pathRows w a p i).2.stk k).length ≤
      (capacityPolynomial w).eval (ea.encode a).length := by
  have hinit : ∀ j, ((initList (computer w) (ea.encode a)).stk j).length ≤ (ea.encode a).length := by
    intro j
    have h := Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound (computer w) (ea.encode a) 0 j
    simpa only [Function.iterate_zero_apply,Nat.zero_mul,Nat.add_zero] using h
  have h := (machine w).run_stack_bound i.val _ _ (ea.encode a).length hinit
    (pathRows_run w a p i)
  have hi : i.val ≤ time w a := by omega
  have ht := Nat.mul_le_mul_right (machine w).pushBudget hi
  exact (h k).trans (by
    simpa [capacityPolynomial,time] using Nat.add_le_add_left ht (ea.encode a).length)

def primitivePolynomial : Polynomial ℕ := timePolynomial w * Polynomial.C (machine w).primitiveBudget

theorem primitive_bound (a : α) (log : List Bool) :
    (machine w).primitiveCost (time w a) (log,initList (computer w) (ea.encode a)) ≤
      (primitivePolynomial w).eval (ea.encode a).length := by
  simpa [primitivePolynomial,time] using (machine w).primitiveCost_le (time w a)
    (log,initList (computer w) (ea.encode a))

theorem primitive_prefix_bound (a : α) (log : List Bool) (j : ℕ) (hj : j ≤ time w a) :
    (machine w).primitiveCost j (log,initList (computer w) (ea.encode a)) ≤
      (primitivePolynomial w).eval (ea.encode a).length := by
  exact ((machine w).primitiveCost_le j _).trans (by
    simpa [primitivePolynomial,time] using Nat.mul_le_mul_right (machine w).primitiveBudget hj)

def storagePolynomial : Polynomial ℕ := Polynomial.C (machine w).controlBits +
  capacityPolynomial w * Polynomial.C (machine w).symbolWidths

theorem temporary_bits (a : α) (p : AcceptedPath w a) (i : Fin (time w a + 1)) :
    (machine w).storageBits (pathRows w a p i).2 ≤
      (storagePolynomial w).eval (ea.encode a).length := by
  simpa [storagePolynomial] using (machine w).storageBits_le (pathRows w a p i).2
    ((capacityPolynomial w).eval (ea.encode a).length) (pathRows_capacity w a p i)

/-- Actual fixed-time lists of labelled TM2 edges, including the unique none
edges after halt. Intermediate configurations satisfy real step equations. -/
abbrev PhysicalPath (a : α) := {bits : List (Option Bool) // bits.length = time w a ∧
  (machine w).TraceValid bits (initList (computer w) (ea.encode a)) (terminal w true)}

def physicalTokens (a : α) (p : AcceptedPath w a) : List (Option Bool) :=
  Classical.choose ((machine w).run_trace (time w a)
    (p.val,initList (computer w) (ea.encode a)) ([],terminal w true) p.property)

theorem physicalTokens_spec (a : α) (p : AcceptedPath w a) :
    (physicalTokens w a p).length = time w a ∧
      (physicalTokens w a p).filterMap id = p.val ∧
      (machine w).TraceValid (physicalTokens w a p)
        (initList (computer w) (ea.encode a)) (terminal w true) := by
  have h := Classical.choose_spec ((machine w).run_trace (time w a)
    (p.val,initList (computer w) (ea.encode a)) ([],terminal w true) p.property)
  simpa only [physicalTokens,List.append_nil] using h

def physicalOfPath (a : α) (p : AcceptedPath w a) : PhysicalPath w a :=
  ⟨physicalTokens w a p,(physicalTokens_spec w a p).1,(physicalTokens_spec w a p).2.2⟩

def pathOfPhysical (a : α) (q : PhysicalPath w a) : AcceptedPath w a :=
  ⟨q.val.filterMap id,by
    have h := ((machine w).reify_trace q.val _ _ q.property.2).1
    rw [q.property.1] at h
    exact h⟩

/-- Both directions are derived from physical step equations. No arbitrary
trajectory extension or unique-execution hypothesis is a source argument. -/
def physicalPathEquiv (a : α) : AcceptedPath w a ≃ PhysicalPath w a where
  toFun := physicalOfPath w a
  invFun := pathOfPhysical w a
  left_inv p := by
    apply Subtype.ext
    exact (physicalTokens_spec w a p).2.1
  right_inv q := by
    apply Subtype.ext
    have hleft := ((machine w).reify_trace (physicalTokens w a (pathOfPhysical w a q))
      _ _ (physicalTokens_spec w a (pathOfPhysical w a q)).2.2).2
    have hright := ((machine w).reify_trace q.val _ _ q.property.2).2
    rw [(physicalTokens_spec w a (pathOfPhysical w a q)).1,
      (physicalTokens_spec w a (pathOfPhysical w a q)).2.1] at hleft
    rw [q.property.1] at hright
    exact hleft.symm.trans hright

def acceptedWitnessPhysicalEquiv (a : α) : AcceptedWitness w a ≃ PhysicalPath w a :=
  (acceptedPathEquiv w a).trans (physicalPathEquiv w a)

noncomputable instance physicalPathFintype (a : α) : Fintype (PhysicalPath w a) :=
  Fintype.ofEquiv (AcceptedPath w a) (physicalPathEquiv w a)

def physicalCount (a : α) : ℕ := Fintype.card (PhysicalPath w a)

theorem physical_count (a : α) : physicalCount w a = f a := by
  calc
    physicalCount w a = pathCount w a := Fintype.card_congr (physicalPathEquiv w a).symm
    _ = f a := path_count w a

/-- Sole concrete forward entry: the physical computation paths, rather than
the verifier predicate by definition, are in a unique count-preserving bijection. -/
theorem witness_forward (a : α) :
    Nonempty (AcceptedWitness w a ≃ PhysicalPath w a) ∧ physicalCount w a = f a :=
  ⟨⟨acceptedWitnessPhysicalEquiv w a⟩,physical_count w a⟩

theorem physical_path_capacity (a : α) (q : PhysicalPath w a)
    (i : Fin (time w a + 1)) (k : (machine w).core.K) :
    ((pathRows w a (pathOfPhysical w a q) i).2.stk k).length ≤
      (capacityPolynomial w).eval (ea.encode a).length :=
  pathRows_capacity w a (pathOfPhysical w a q) i k

theorem physical_path_bits (a : α) (q : PhysicalPath w a) (i : Fin (time w a + 1)) :
    (machine w).codedStorageBits (pathRows w a (pathOfPhysical w a q) i).2 ≤
      (storagePolynomial w).eval (ea.encode a).length :=
  ((machine w).codedStorageBits_le _).trans (temporary_bits w a (pathOfPhysical w a q) i)

theorem physical_path_primitive (a : α) (q : PhysicalPath w a)
    (i : Fin (time w a + 1)) :
    (machine w).primitiveCost i.val
      (q.val.filterMap id,initList (computer w) (ea.encode a)) ≤
        (primitivePolynomial w).eval (ea.encode a).length :=
  primitive_prefix_bound w a (q.val.filterMap id) i.val (by omega)

theorem split_branches_distinct (count input : List Bool)
    (witness : List (w.verifier.tm.Γ w.verifier.tm.k₀)) :
    phaseCfg w 2 count input (w.verifier.inputAlphabet.symm (Sum.inr false) :: witness) ≠
      phaseCfg w 2 count input (w.verifier.inputAlphabet.symm (Sum.inr true) :: witness) :=
  choice_targets_distinct w count input witness

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source
