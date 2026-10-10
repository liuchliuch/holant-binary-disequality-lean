import Holant.Proofs.LinearProgramming.Complexity.CounterLoop.Body

/-! Rational LP physical resource implementation, adapted from the supplied reference.
Semantic result of the actual binary-counter branches. The correctness proof
inducts on the remaining budget and identifies every live machine round with
the SAME rounded trajectory. At exhaustion it uses RoundedTermination, not
a caller-supplied correct timeout. An accepted stored center is a THICKENED
point; it is deliberately not labelled an exact original LP witness.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion
open Holant.LocalDrafts.RemoteWork.RationalLP.Optimization Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search
open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity
open Computability Holant.Algebraic Holant.Complexity BinaryCompose Codec
noncomputable section

def finish : ℕ → StepProgram.Query → State
  | 0,q => stamp 0 (decide (Body.accepted q)) q
  | r+1,q => if Body.accepted q then stamp (r+1) true q
      else if Body.zeroNormal q then stamp (r+1) false q
      else finish r (StepProgram.value q)

theorem accepted_iff (d : Input) (k : ℕ) : Body.accepted (queryAt d k) ↔
    Separation.separate d.val (RoundedTrajectory.run d.val k).center=none := by
  unfold Body.accepted queryAt
  rw [StepProgram.scanner_exact]
  cases Separation.separate d.val (RoundedTrajectory.run d.val k).center <;> simp

theorem zero_rejects (d : Input) (k : ℕ) (ha : ¬Body.accepted (queryAt d k))
    (hz : Body.zeroNormal (queryAt d k)) : ¬∃ x, Feasible d.val x := by
  cases hc : Separation.separate d.val (RoundedTrajectory.run d.val k).center with
  | none => exact False.elim (ha ((accepted_iff d k).mpr hc))
  | some c =>
    have he := StepProgram.normal_exact d (RoundedTrajectory.run d.val k) c hc
    have hg : Separation.normal d.val c=0 := by
      apply (StepProgram.ofFn_zero _).mp
      exact he.symm.trans hz
    exact RoundedTrajectory.rejected_zero d.val k c hc hg

/-- Complete proof on original data, with no correctness or feasible-point
parameter. k+r=N states the countdown invariant, not a solver certificate. -/
theorem correct_from (d : Input) (hn : 2≤d.val.dimension) (r k : ℕ)
    (hbudget : k+r=GridPrecision.iterations d.val) :
    answer (finish r (queryAt d k))=true ↔ ∃ x, Feasible d.val x := by
  induction r generalizing k with
  | zero =>
    have hk : k=GridPrecision.iterations d.val := by omega
    subst k
    simpa only [finish,answer,stamp,accepted_iff,decide_eq_true_eq,RoundedTermination.value]
      using RoundedTermination.correct d.val hn
  | succ r ih =>
    by_cases ha : Body.accepted (queryAt d k)
    · simp only [finish,if_pos ha,answer,stamp]
      exact iff_of_true True.intro (RoundedTrajectory.accepted d.val k ((accepted_iff d k).mp ha))
    · by_cases hz : Body.zeroNormal (queryAt d k)
      · simp only [finish,if_neg ha,if_pos hz,answer,stamp]
        exact iff_of_false Bool.false_ne_true (zero_rejects d k ha hz)
      · have hstep := actual_round d hn k (by omega)
        rw [finish,if_neg ha,if_neg hz,hstep]
        exact ih (k+1) (by omega)

/-- Every output word contains the original input and an actually reached
rounded state, not a freshly selected solution. This also supplies the
uniform stored-word bound for stop branches and intermediate transfers. -/
theorem trace (d : Input) (hn : 2≤d.val.dimension) (r k : ℕ)
    (hbudget : k+r≤GridPrecision.iterations d.val) :
    ∃ j u, k≤j ∧ j≤k+r ∧ u≤r ∧
      finish r (queryAt d k)=stamp u (decide (Body.accepted (queryAt d j))) (queryAt d j) := by
  induction r generalizing k with
  | zero => exact ⟨k,0,le_rfl,by omega,le_rfl,rfl⟩
  | succ r ih =>
    by_cases ha : Body.accepted (queryAt d k)
    · refine ⟨k,r+1,le_rfl,by omega,le_rfl,?_⟩
      simp [finish,ha]
    · by_cases hz : Body.zeroNormal (queryAt d k)
      · refine ⟨k,r+1,le_rfl,by omega,le_rfl,?_⟩
        simp [finish,ha,hz]
      · obtain ⟨j,u,hj,hjr,hu,he⟩ := ih (k+1) (by omega)
        refine ⟨j,u,by omega,by omega,by omega,?_⟩
        rw [finish,if_neg ha,if_neg hz,actual_round d hn k (by omega)]
        exact he

def resultState (d : Input) : State := finish (GridPrecision.iterations d.val) (initialQuery d)
def result (d : Input) : Bool := answer (resultState d)

theorem correct (d : Input) (hn : 2≤d.val.dimension) : result d=true ↔ ∃ x, Feasible d.val x := by
  unfold result resultState
  rw [initialQuery_exact]
  exact correct_from d hn _ 0 (by omega)

theorem result_trace (d : Input) (hn : 2≤d.val.dimension) :
    ∃ j u, j≤GridPrecision.iterations d.val ∧ u≤GridPrecision.iterations d.val ∧
      resultState d=stamp u (decide (Body.accepted (queryAt d j))) (queryAt d j) := by
  obtain ⟨j,u,hj,hjr,hu,he⟩ := trace d hn (GridPrecision.iterations d.val) 0 (by omega)
  exact ⟨j,u,by omega,hu,by simpa only [resultState,initialQuery_exact] using he⟩

theorem source_preserved (d : Input) (hn : 2≤d.val.dimension) : (query (resultState d)).1=d := by
  obtain ⟨j,u,hj,hu,he⟩ := result_trace d hn
  rw [he]
  rfl

/-- Precise recovery interface: a physically returned thickened center and
its original matrix. Exact Codec.Response reconstruction remains separate. -/
theorem accepted_center (d : Input) (hn : 2≤d.val.dimension) (ha : result d=true) :
    Thickening.At d.val (Thickening.epsilon d.val)
      (StorageProgram.decode d.val.dimension (query (resultState d)).2).center := by
  obtain ⟨j,u,hj,hu,he⟩ := result_trace d hn
  have hs : Body.accepted (queryAt d j) := by
    simpa only [result,he,answer,stamp,decide_eq_true_eq] using ha
  have hsep := (accepted_iff d j).mp hs
  rw [he]
  change Thickening.At _ _ (StorageProgram.decode _ (StorageProgram.code (RoundedTrajectory.run d.val j))).center
  rw [StorageProgram.decode_code]
  exact (Separation.none_iff d.val _).mp hsep

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
