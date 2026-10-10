import Holant.Proofs.Algorithms.OneQueryControl
import Holant.Complexity.OracleOneQuery.ContextReduction
import Holant.Complexity.OracleReductionCompose


namespace Holant.LocalDrafts.Hardness.ContextControl
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines OracleOneQuery.Context
open Holant.LocalDrafts.MainChain.OneQueryControl

variable (a b : BinaryCompose.Machine)

def Past : Option (Labels a b) → Prop
  | none => True
  | some (.inl _) => False
  | some (.inr (.inl _)) => True
  | some (.inr (.inr i)) => 3 ≤ i.val

theorem isQuery_iff (c : Config a b) :
    (machine a b).IsQuery c ↔ c.l = some (admin a b 2) := by
  constructor
  · rintro ⟨label,next,hl,hp⟩
    rcases label with l | (l | i)
    · simp [machine, program] at hp
    · simp [machine, program] at hp
    · fin_cases i <;> simp [machine, program, admin] at hp ⊢
      exact hl
  · intro hl
    exact ⟨admin a b 2, (fun _ => admin a b 3), hl, rfl⟩

theorem past_step (oracle : List Bool → List Bool) (c : Config a b)
    (hc : Past a b c.l) :
    ((machine a b).step oracle c).elim True (fun d => Past a b d.l) := by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => trivial
  | some label =>
    rcases label with l | (l | i)
    · exact False.elim hc
    · exact embedStmt_label (a.rightLayout b) (a.rightStates b)
        (secondLabel a b) none (Past a b) (fun _ => True.intro)
        True.intro (b.program l) state tapes
    · fin_cases i
      · simp [Past] at hc
      · simp [Past] at hc
      · simp [Past] at hc
      · exact copyMove_label (a.destinationKey b) (a.temporaryKey b)
          (admin a b 3) (admin a b 4) (Past a b) (by norm_num [Past, admin]) (by norm_num [Past, admin]) state tapes
      · simp [machine, program, admin, OracleMachine.step,
          FrameEmit.delimiterStmt, TM2.stepAux, Past]
      · change Past a b (TM2.stepAux
          (FrameEmit.emitStmt (a.temporaryKey b) (a.sourceKey b)
            (admin a b 5) (admin a b 6)) state tapes).l
        simp only [FrameEmit.emitStmt, TM2.stepAux]
        cases h : (tapes (a.temporaryKey b)).head?.isSome <;> simp [h, Past, admin]
      · exact copyMove_label (a.sourceKey b) (a.temporaryKey b)
          (admin a b 6) (admin a b 7) (Past a b) (by norm_num [Past, admin]) (by norm_num [Past, admin]) state tapes
      · exact copyMove_label (a.temporaryKey b) (a.destinationKey b)
          (admin a b 7) (secondLabel a b b.main) (Past a b)
          (by norm_num [Past, admin]) True.intro state tapes
      · trivial

theorem query_step_past (oracle : List Bool → List Bool) (c : Config a b)
    (hq : (machine a b).IsQuery c) :
    ((machine a b).step oracle c).elim True (fun d => Past a b d.l) := by
  have hl := (isQuery_iff a b c).mp hq
  rcases c with ⟨label,state,tapes⟩
  dsimp at hl
  subst label
  simp [machine, OracleMachine.step, program, admin, Past]

theorem past_iterate (oracle : List Bool → List Bool) (u : Option (Config a b))
    (hu : u.elim True (fun c => Past a b c.l)) (k : ℕ) :
    ((fun p => p.bind ((machine a b).step oracle))^[k] u).elim
      True (fun c => Past a b c.l) := by
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
    (hd : (machine a b).run oracle input (k + (n+1)) = some d) :
    ¬ (machine a b).IsQuery d := by
  have hp := past_iterate a b oracle ((machine a b).step oracle c)
    (query_step_past a b oracle c hc) k
  have he : (machine a b).run oracle input (k + (n+1)) =
      (fun p => p.bind ((machine a b).step oracle))^[k]
        ((machine a b).step oracle c) := by
    unfold OracleMachine.run
    rw [Function.iterate_add_apply]
    change (fun p => p.bind ((machine a b).step oracle))^[k]
      ((machine a b).run oracle input (n+1)) = _
    rw [OracleMachine.run_succ, hn, Option.bind_some]
  rw [← he, hd] at hp
  intro hq
  have hl := (isQuery_iff a b d).mp hq
  simpa [hl, admin, Past] using hp

def queryCfg (query context : List Bool) : Config a b :=
  StackProtocol.cfg (admin a b 2) (a.initial,b.initial)
    (StackProtocol.tapes3 (fun _ => []) (a.sourceKey b) (a.destinationKey b)
      (a.temporaryKey b) context query [])

theorem parse_to_query (oracle : List Bool → List Bool) (query context : List Bool) :
    StackProtocol.RunsExactly ((machine a b).step oracle)
      (leftCfg a b (haltList a.computer (frame query ++ context)))
      (queryCfg a b query context) (2 * (query.length+1)) := by
  rw [left_halt]
  have h := GraphPreprocessing.Frame.extract_exact
    (a.sourceKey b) (a.destinationKey b) (a.temporaryKey b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b 0) (admin a b 1) (admin a b 2)
    (admin a b 8) (by intro state tapes; rfl) (by intro state tapes; rfl)
    (a.initial,b.initial) (fun _ => []) query context []
  have ht : StackProtocol.tapes3 (fun _ : Keys a b => []) (a.sourceKey b)
      (a.destinationKey b) (a.temporaryKey b) (frame query ++ context) [] [] =
      wordTape (a.sourceKey b) (frame query ++ context) := by
    funext k
    cases k with
    | inl k => simp [StackProtocol.tapes3, Machine.sourceKey, Machine.destinationKey,
        Machine.temporaryKey, wordTape, Function.update_apply]
    | inr k => cases k <;> simp [StackProtocol.tapes3, Machine.sourceKey,
        Machine.destinationKey, Machine.temporaryKey, wordTape, Function.update_apply]
  simpa only [ht, List.append_nil, queryCfg] using h

/-- Every actual query state is the original compiler's query word, with its
counter/context on a different tape. Holds even for arbitrary oracle extensions. -/
theorem query_configuration (oracle : List Bool → List Bool)
    (input query context : List Bool) (n t : ℕ) (c : Config a b)
    (ha : (fun p => p.bind a.computer.step)^[n] (some (initList a.computer input)) =
      some (haltList a.computer (frame query ++ context)))
    (hr : (machine a b).run oracle input t = some c)
    (hq : (machine a b).IsQuery c) : c = queryCfg a b query context := by
  let qtime := 2 * (query.length+1) + n
  have hn : (machine a b).run oracle input qtime = some (queryCfg a b query context) := by
    have h := OracleOneQuery.ordinary_run (M := machine a b) (a.leftLayout b) (a.leftStates b)
      (firstLabel a b) (some (admin a b 0)) (fun _ => rfl) oracle _ _ n ha
    change (fun p => p.bind ((machine a b).step oracle))^[n]
      (some (leftCfg a b _)) = some (leftCfg a b _) at h
    rw [left_init] at h
    unfold OracleMachine.run
    rw [show qtime = 2 * (query.length+1) + n from rfl,
      Function.iterate_add_apply, h]
    exact parse_to_query a b oracle query context
  have hqn : (machine a b).IsQuery (queryCfg a b query context) :=
    (isQuery_iff a b _).mpr rfl
  have ht : t = qtime := by
    rcases lt_trichotomy t qtime with h | h | h
    · have he : qtime = (qtime-(t+1))+(t+1) := by omega
      exact False.elim ((no_later_query a b oracle input t (qtime-(t+1)) c _ hr hq
        (by simpa only [← he] using hn)) hqn)
    · exact h
    · have he : t = (t-(qtime+1))+(qtime+1) := by omega
      exact False.elim ((no_later_query a b oracle input qtime (t-(qtime+1)) _ c hn hqn
        (by simpa only [← he] using hr)) hq)
  subst t
  exact Option.some.inj (hr.symm.trans hn)

end Holant.LocalDrafts.Hardness.ContextControl
