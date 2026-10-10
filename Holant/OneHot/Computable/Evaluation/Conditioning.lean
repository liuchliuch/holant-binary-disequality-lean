import Holant.OneHot.Computable.Evaluation.FiniteIndex
import Holant.OneHot.Decomposition.UnicycleEvaluation

/-! Executable deletion/conditioning of both original occurrences of one edge. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.FiniteNetwork

variable {K V E : Type*} [DecidableEq E] (N : FiniteNetwork K V E 0)

/-- Decide survival by the actual original edge ID. -/
def executableRemainingPorts (e : E) (v : V) : Finset (Fin (N.arity v)) :=
  Finset.univ.filter (fun i => (N.closedPorts ⟨v, i⟩).1 ≠ e)

@[simp] theorem executableRemainingPorts_eq (e : E) (v : V) :
    N.executableRemainingPorts e v = N.remainingPorts e v := by
  classical
  ext i
  simp [executableRemainingPorts, mem_remainingPorts]

/-- Deterministic increasing enumeration of the surviving original local ports. -/
def executableRemainingPortEquiv (e : E) (v : V) :
    Fin (N.executableRemainingPorts e v).card ≃ N.RemainingPort e v :=
  ((N.executableRemainingPorts e v).orderIsoOfFin rfl).toEquiv.trans
    (Equiv.subtypeEquivRight (fun i => by simp [executableRemainingPorts]))

/-- Restore the two independently selected bits at their own original occurrences. -/
def executableConditionWord (e : E) (a b : Bool) (v : V)
    (x : Fin (N.executableRemainingPorts e v).card → Bool) : Fin (N.arity v) → Bool :=
  fun i => if h : (N.closedPorts ⟨v, i⟩).1 = e then
    (if (N.closedPorts ⟨v, i⟩).2 then b else a)
    else x ((N.executableRemainingPortEquiv e v).symm ⟨i, h⟩)

/-- Generic finite-port assembly, with its completeness proof erased at runtime. -/
def conditionUsing (e : E) (a b : Bool)
    (ps : {ps : (v : V) → Finset (Fin (N.arity v)) //
      ∀ v i, i ∈ ps v ↔ (N.closedPorts ⟨v, i⟩).1 ≠ e}) :
    FiniteNetwork K V (RemainingEdge e) 0 :=
  let pe (v : V) : Fin (ps.1 v).card ≃ N.RemainingPort e v :=
    ((ps.1 v).orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight (ps.2 v))
  { arity := fun v => (ps.1 v).card
    ports := (Equiv.sigmaCongrRight pe).trans
      ((N.remainingClosedPorts e).trans (Equiv.emptySum (Fin 0) _).symm)
    vertex := fun v x => N.vertex v (fun i =>
      if h : (N.closedPorts ⟨v, i⟩).1 = e then
        (if (N.closedPorts ⟨v, i⟩).2 then b else a)
      else x ((pe v).symm ⟨i, h⟩))
    edge := fun d => N.edge d.1 }

/-- A genuine computed residual graph. Every surviving edge ID, vertex, local
port order and orientation is retained; loops lose both distinct occurrences. -/
def executableConditionEdge (e : E) (a b : Bool) : FiniteNetwork K V (RemainingEdge e) 0 :=
  N.conditionUsing e a b ⟨N.executableRemainingPorts e,
    fun v i => by simp [executableRemainingPorts]⟩

/-- The executed constructor agrees with the independently verified semantic
conditioning operation, including all ordered port data. -/
theorem executableConditionEdge_eq (e : E) (a b : Bool) :
    N.executableConditionEdge e a b = N.conditionEdge e a b := by
  have hp :
      (⟨N.executableRemainingPorts e, fun v i => by simp [executableRemainingPorts]⟩ :
        {ps : (v : V) → Finset (Fin (N.arity v)) //
          ∀ v i, i ∈ ps v ↔ (N.closedPorts ⟨v, i⟩).1 ≠ e}) =
      ⟨N.remainingPorts e, N.mem_remainingPorts e⟩ :=
    Subtype.ext (funext (N.executableRemainingPorts_eq e))
  unfold executableConditionEdge
  rw [hp]
  unfold conditionUsing conditionEdge conditionWord remainingPortEquiv
  dsimp only
  congr 1
  funext v x
  apply congrArg (N.vertex v)
  funext i
  by_cases hi : (N.closedPorts ⟨v, i⟩).1 = e <;> simp only [hi, ↓reduceDIte]

end Holant.FiniteNetwork
