import Holant.Complexity.OracleOneQuery.Reduction

/-!
One-query control-flow proof, ported into the isolated CountingBridge task.

The existing one-query machine has a timed correctness proof.  Here its actual
control flow supplies the additional query-safety contract needed by reduction
composition.  In particular no claim about malformed oracle queries is assumed.
-/

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
open Turing Computability Holant.Complexity
open Holant.Complexity.BinaryCompose Holant.Complexity.OracleOneQuery

variable (a b : BinaryCompose.Machine)

/-- The decoder and transfer phases cannot return to the input compiler/query. -/
def PastQuery : Option (Labels a b) → Prop
  | none => True
  | some (.inl _) => False
  | some (.inr (.inl _)) => True
  | some (.inr (.inr none)) => False
  | some (.inr (.inr (some _))) => True

theorem isQuery_iff (c : Config a b) :
    (machine a b).IsQuery c ↔ c.l = some (queryLabel a b) := by
  constructor
  · rintro ⟨label, next, hl, hp⟩
    rcases label with l | (l | o)
    · simp [machine, program] at hp
    · simp [machine, program] at hp
    · cases o with
      | none => exact hl
      | some bit => cases bit <;> simp [machine, program] at hp
  · intro hl
    exact ⟨queryLabel a b, (fun _ => moveLabel a b), hl, rfl⟩

/-- A syntax-level return-label fact, valid even for arbitrary ambient tapes. -/
theorem embedStmt_label {K J Λ R σ τ : Type} [DecidableEq K] [DecidableEq J]
    (layout : StackEmbedding K J) (states : StateEmbedding σ τ)
    (labels : Λ → R) (stop : Option R) (P : Option R → Prop)
    (hlabels : ∀ l, P (some (labels l))) (hstop : P stop)
    (stmt : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : τ) (tapes : J → List Bool) :
    P (TM2.stepAux (embedStmt layout states labels stop stmt) state tapes).l := by
  induction stmt generalizing state tapes with
  | push k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    simp only [embedStmt, TM2.stepAux]
    cases hb : f (states.get state) with
    | false => simpa only [hb, Bool.cond_false] using ihr state tapes
    | true => simpa only [hb, Bool.cond_true] using ihq state tapes
  | goto f => exact hlabels _
  | halt => cases stop <;> exact hstop

theorem copyMove_label {K Λ τ : Type} [DecidableEq K]
    (src dst : K) (loop next : Λ) (P : Option Λ → Prop)
    (hl : P (some loop)) (hn : P (some next))
    (state : Option Bool × τ) (tapes : K → List Bool) :
    P (TM2.stepAux (StackProtocol.copyMoveStmt src dst loop next) state tapes).l := by
  simp only [StackProtocol.copyMoveStmt, TM2.stepAux]
  cases hb : (tapes src).head?.isSome with
  | false => simpa only [hb, Bool.cond_false] using hn
  | true => simpa only [hb, Bool.cond_true] using hl

theorem past_step (oracle : List Bool → List Bool) (c : Config a b)
    (hc : PastQuery a b c.l) :
    ((machine a b).step oracle c).elim True (fun d => PastQuery a b d.l) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => trivial
  | some label =>
    rcases label with l | (l | o)
    · exact False.elim hc
    · exact embedStmt_label (a.rightLayout b) (a.rightStates b)
        (secondLabel a b) none (PastQuery a b) (fun _ => True.intro)
        True.intro (b.program l) state tapes
    · cases o with
      | none => exact False.elim hc
      | some bit =>
        cases bit with
        | false =>
          exact copyMove_label (a.sourceKey b) (a.temporaryKey b)
            (moveLabel a b) (restoreLabel a b) (PastQuery a b)
            True.intro True.intro state tapes
        | true =>
          exact copyMove_label (a.temporaryKey b) (a.destinationKey b)
            (restoreLabel a b) (secondLabel a b b.main) (PastQuery a b)
            True.intro True.intro state tapes

theorem query_step_past (oracle : List Bool → List Bool) (c : Config a b)
    (hq : (machine a b).IsQuery c) :
    ((machine a b).step oracle c).elim True (fun d => PastQuery a b d.l) := by
  have hl := (isQuery_iff a b c).mp hq
  rcases c with ⟨label, state, tapes⟩
  dsimp at hl
  subst label
  trivial

theorem past_iterate (oracle : List Bool → List Bool) (u : Option (Config a b))
    (hu : u.elim True (fun c => PastQuery a b c.l)) (k : ℕ) :
    ((fun p => p.bind ((machine a b).step oracle))^[k] u).elim
      True (fun c => PastQuery a b c.l) := by
  induction k with
  | zero => exact hu
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    cases h : (fun p => p.bind ((machine a b).step oracle))^[k] u with
    | none => trivial
    | some c =>
      simp only [h, Option.elim_some] at ih
      exact past_step a b oracle c ih

theorem no_later_query (oracle : List Bool → List Bool) (input : List Bool)
    (n k : ℕ) (c d : Config a b)
    (hn : (machine a b).run oracle input n = some c)
    (hc : (machine a b).IsQuery c)
    (hd : (machine a b).run oracle input (k + (n + 1)) = some d) :
    ¬ (machine a b).IsQuery d := by
  have hp := past_iterate a b oracle ((machine a b).step oracle c)
    (query_step_past a b oracle c hc) k
  have he : (fun p => p.bind ((machine a b).step oracle))^[k]
      ((machine a b).step oracle c) = some d := by
    have he0 : (machine a b).run oracle input (k + (n + 1)) =
        (fun p => p.bind ((machine a b).step oracle))^[k]
          ((machine a b).step oracle c) := by
      unfold OracleMachine.run
      rw [Function.iterate_add_apply]
      change (fun p => p.bind ((machine a b).step oracle))^[k]
        ((machine a b).run oracle input (n + 1)) = _
      rw [OracleMachine.run_succ, hn, Option.bind_some]
    exact he0.symm.trans hd
  rw [he] at hp
  intro hq
  have hl := (isQuery_iff a b d).mp hq
  simpa only [Option.elim_some, hl, queryLabel, PastQuery] using hp

/-- The unique reachable query is exactly the clean compiler output. -/
theorem query_configuration (oracle : List Bool → List Bool)
    (input query : List Bool) (n t : ℕ) (c : Config a b)
    (ha : (fun p => p.bind a.computer.step)^[n] (some (initList a.computer input)) =
      some (haltList a.computer query))
    (hr : (machine a b).run oracle input t = some c)
    (hq : (machine a b).IsQuery c) :
    c = leftCfg a b (haltList a.computer query) := by
  have hn : (machine a b).run oracle input n =
      some (leftCfg a b (haltList a.computer query)) := by
    have h := ordinary_run (M := machine a b) (a.leftLayout b) (a.leftStates b)
      (firstLabel a b) (some (queryLabel a b)) (fun _ => rfl) oracle _ _ n ha
    change (fun p => p.bind ((machine a b).step oracle))^[n]
      (some (leftCfg a b _)) = _ at h
    rw [left_init] at h
    exact h
  have hqn : (machine a b).IsQuery (leftCfg a b (haltList a.computer query)) := by
    apply (isQuery_iff a b _).mpr
    rw [left_halt]
    rfl
  have ht : t = n := by
    rcases lt_trichotomy t n with h | h | h
    · have hn' : n = (n - (t + 1)) + (t + 1) := by omega
      exact False.elim ((no_later_query a b oracle input t (n - (t + 1)) c _
        hr hq (by simpa only [← hn'] using hn)) hqn)
    · exact h
    · have ht' : t = (t - (n + 1)) + (n + 1) := by omega
      exact False.elim ((no_later_query a b oracle input n (t - (n + 1)) _ c
        hn hqn (by simpa only [← ht'] using hr)) hq)
  subst t
  exact Option.some.inj (hr.symm.trans hn)

end Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
