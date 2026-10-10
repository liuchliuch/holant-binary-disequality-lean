import Holant.Proofs.LinearProgramming.Complexity.CounterLoop.Source

/-! Rational LP physical resource implementation, adapted from the supplied reference.
Actual control-bit and binary-counter invariants, including the final budget
scan. Every live transfer advances precisely one original rounded state and
decrements precisely one binary unit. Every false flag already gives a sound
Boolean at that state: accepted, selected zero normal, or the actual N-th
center. The native transfer and stop lemmas below consume actual Body outputs,
not a correct solver or an expected whole-loop execution supplied by a caller.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion
open Holant.LocalDrafts.RemoteWork.RationalLP.Optimization Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search
open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose StackProtocol Codec
namespace ControlInvariant
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
noncomputable section

theorem live_iff (r : ℕ) (b : Bool) (q : StepProgram.Query) :
    (Body.value (stamp r b q)).1=true ↔
      ¬Body.accepted q ∧ ¬Body.zeroNormal q ∧ 0<r := by
  by_cases ha : Body.accepted q <;> by_cases hz : Body.zeroNormal q <;>
    by_cases hr : r=0 <;>
    simp [Body.value,Body.stopped,Body.advanced,stamp,query,remaining,ha,hz,hr,Nat.pos_iff_ne_zero]

/-- The conservation equation is produced, not passed as a next-state
invariant by the caller. The header flag is the actual Body result. -/
theorem live_next (d : Input) (hn : 2≤d.val.dimension) (k r : ℕ) (b : Bool)
    (hbudget : k+r=GridPrecision.iterations d.val)
    (hflag : (Body.value (stamp r b (queryAt d k))).1=true) :
    0<r ∧ (Body.value (stamp r b (queryAt d k))).2=
      stamp (r-1) false (queryAt d (k+1)) ∧
      (k+1)+(r-1)=GridPrecision.iterations d.val := by
  obtain ⟨ha,hz,hr⟩ := (live_iff r b (queryAt d k)).mp hflag
  have hstep := actual_round d hn k (by omega)
  cases r with
  | zero => omega
  | succ r =>
    rw [Body.active r b _ ha hz,hstep]
    exact ⟨hr,rfl,by omega⟩

/-- A real stop header is sufficient for its answer; no terminal correctness
certificate or claimed iteration history is attached to the input word. -/
theorem stop_correct (d : Input) (hn : 2≤d.val.dimension) (k r : ℕ) (b : Bool)
    (hbudget : k+r=GridPrecision.iterations d.val)
    (hflag : (Body.value (stamp r b (queryAt d k))).1=false) :
    answer ((Body.value (stamp r b (queryAt d k))).2)=true ↔ ∃ x, Feasible d.val x := by
  by_cases ha : Body.accepted (queryAt d k)
  · rw [Body.accepted_stop _ _ _ ha]
    exact iff_of_true rfl (RoundedTrajectory.accepted d.val k ((accepted_iff d k).mp ha))
  · by_cases hz : Body.zeroNormal (queryAt d k)
    · rw [Body.zero_stop _ _ _ ha hz]
      exact iff_of_false Bool.false_ne_true (zero_rejects d k ha hz)
    · have hr : r=0 := by
        have ht := Body.flag_false_iff (stamp r b (queryAt d k))
        have hcases := ht.mp hflag
        simpa only [remaining,query,stamp,ha,hz,false_or] using hcases
      subst r
      have hk : k=GridPrecision.iterations d.val := by omega
      rw [Body.zero]
      change decide (Body.accepted (queryAt d k))=true ↔ _
      rw [decide_eq_true_eq,accepted_iff,hk]
      have hc := RoundedTermination.correct d.val hn
      simpa only [RoundedTermination.value,decide_eq_true_eq] using hc

/-- Explicit native transition from the original k-th word to the k+1-th
word with its decremented binary counter. -/
theorem native_continue (d : Input) (hn : 2≤d.val.dimension) (k r : ℕ) (b : Bool)
    (hbudget : k+(r+1)=GridPrecision.iterations d.val)
    (ha : ¬Body.accepted (queryAt d k)) (hz : ¬Body.zeroNormal (queryAt d k)) :
    RunsExactly Native.machine.computer.step
      (Native.ready (stamp (r+1) b (queryAt d k)))
      (Native.ready (stamp r false (queryAt d (k+1))))
      ((Body.computes.outputs (stamp (r+1) b (queryAt d k))).steps+
        2*(encoding.encode (stamp r false (queryAt d (k+1)))).length+3) := by
  apply ReturningLoop.continue_run Body.computes.machine Body.disjoint
  apply Native.body_continue
  rw [Body.active r b _ ha hz,actual_round d hn k (by omega)]

/-- Native stop transfers the actual stamped word, clears work stacks, and
halts. Its Boolean postcondition follows from stop_correct above. -/
theorem native_stop (d : Input) (hn : 2≤d.val.dimension) (k r : ℕ) (b : Bool)
    (hbudget : k+r=GridPrecision.iterations d.val)
    (hflag : (Body.value (stamp r b (queryAt d k))).1=false) :
    RunsExactly Native.machine.computer.step
      (Native.ready (stamp r b (queryAt d k)))
      (haltList Native.machine.computer
        (encoding.encode ((Body.value (stamp r b (queryAt d k))).2)))
      ((Body.computes.outputs (stamp r b (queryAt d k))).steps+
        2*(encoding.encode ((Body.value (stamp r b (queryAt d k))).2)).length+4) := by
  apply ReturningLoop.stop_run Body.computes.machine
  apply Native.body_stop
  exact Prod.ext hflag rfl

/-- Strong terminal trace: the binary remaining count equals original
budget minus exactly the number of active rounded updates. -/
theorem exact_trace (d : Input) (hn : 2≤d.val.dimension) (r k : ℕ)
    (hbudget : k+r≤GridPrecision.iterations d.val) :
    ∃ j, k≤j ∧ j≤k+r ∧ finish r (queryAt d k)=
      stamp (k+r-j) (decide (Body.accepted (queryAt d j))) (queryAt d j) := by
  induction r generalizing k with
  | zero => refine ⟨k,le_rfl,by omega,?_⟩; simp [finish]
  | succ r ih =>
    by_cases ha : Body.accepted (queryAt d k)
    · refine ⟨k,le_rfl,by omega,?_⟩
      simp [finish,ha,Nat.add_sub_cancel_left]
    · by_cases hz : Body.zeroNormal (queryAt d k)
      · refine ⟨k,le_rfl,by omega,?_⟩
        simp [finish,ha,hz,Nat.add_sub_cancel_left]
      · obtain ⟨j,hj,hjr,he⟩ := ih (k+1) (by omega)
        refine ⟨j,by omega,by omega,?_⟩
        rw [finish,if_neg ha,if_neg hz,actual_round d hn k (by omega),he]
        congr 1
        omega

theorem terminal_counter (d : Input) (hn : 2≤d.val.dimension) :
    ∃ j, j≤GridPrecision.iterations d.val ∧ resultState d=
      stamp (GridPrecision.iterations d.val-j)
        (decide (Body.accepted (queryAt d j))) (queryAt d j) := by
  obtain ⟨j,hj,hjr,he⟩ := exact_trace d hn (GridPrecision.iterations d.val) 0 (by omega)
  exact ⟨j,by omega,by simpa only [resultState,initialQuery_exact,zero_add] using he⟩

end
end ControlInvariant
end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
