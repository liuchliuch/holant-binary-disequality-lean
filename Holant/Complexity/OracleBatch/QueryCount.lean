import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ThreeQueryCount
import Holant.Complexity.OracleOneQuery.Program

namespace Holant.Complexity.OracleBatch
open Turing BinaryCompose
open UniversalPairReduction.ThreeQuery

/-- Erase oracle transitions for proof purposes. This relation is used only to
certify ordinary segments of the actual caller; it is not a machine opcode. -/
def ordinaryStep (m : OracleMachine) : m.Cfg → Option m.Cfg
  | ⟨none,_,_⟩ => none
  | ⟨some l,v,s⟩ => match m.program l with
    | .ordinary stmt => some (TM2.stepAux stmt v s)
    | .query _ => none

theorem ordinaryStep_spec (m : OracleMachine) (oracle : List Bool → List Bool)
    (c d : m.Cfg) (h : ordinaryStep m c = some d) :
    m.step oracle c = some d ∧ queryCost m c = 0 := by
  rcases c with ⟨l,v,s⟩
  cases l with
  | none => simp [ordinaryStep] at h
  | some l =>
    cases hp : m.program l <;> simp [ordinaryStep,hp] at h
    next stmt => exact ⟨by simpa [OracleMachine.step,hp] using h, by simp [queryCost,hp]⟩

@[simp] theorem iterate_bind_none {C : Type} (step : C → Option C) (n : ℕ) :
    (fun p => p.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply,Option.bind_none] using ih

theorem queryCount_add (m : OracleMachine) (oracle : List Bool → List Bool)
    (c d : m.Cfg) (n k : ℕ)
    (h : (fun p => p.bind (m.step oracle))^[n] (some c) = some d) :
    queryCount m oracle c (n+k) = queryCount m oracle c n + queryCount m oracle d k := by
  induction n generalizing c with
  | zero => have hd := Option.some.inj h; subst d; simp [queryCount]
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : m.step oracle c with
    | none => simp [hs] at h
    | some e =>
      simp only [Option.bind_some,hs] at h
      simpa [Nat.succ_add,queryCount,hs,Nat.add_assoc] using congrArg
        (fun x => queryCost m c + x) (ih e h)

/-- A certified ordinary segment contains exactly zero real oracle calls. -/
theorem ordinary_run_count (m : OracleMachine) (oracle : List Bool → List Bool)
    (c d : m.Cfg) (n : ℕ)
    (h : (fun p => p.bind (ordinaryStep m))^[n] (some c) = some d) :
    (fun p => p.bind (m.step oracle))^[n] (some c) = some d ∧ queryCount m oracle c n = 0 := by
  induction n generalizing c with
  | zero => exact ⟨h,rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : ordinaryStep m c with
    | none => simp [hs] at h
    | some e =>
      simp only [Option.bind_some,hs] at h
      have he := ordinaryStep_spec m oracle c e hs
      have hr := ih e h
      constructor
      · simpa [Function.iterate_succ_apply,he.1] using hr.1
      · simp [queryCount,he.1,he.2,hr.2]

/-- Structurally embedded ordinary machines also run in the erased relation. -/
theorem embedded_ordinary_run {m : BinaryCompose.Machine} {M : OracleMachine}
    (layout : StackEmbedding m.K M.K) (states : StateEmbedding m.State M.σ)
    (labels : m.Label → M.Λ) (stop : Option M.Λ)
    (agree : ∀ l, M.program (labels l) = .ordinary
      (embedStmt layout states labels stop (m.program l)))
    (c d : m.Config) (n : ℕ)
    (h : (fun p => p.bind m.computer.step)^[n] (some c) = some d) :
    (fun p => p.bind (ordinaryStep M))^[n]
      (some (embedCfg layout states labels stop c)) = some (embedCfg layout states labels stop d) := by
  change (fun p => p.bind (TM2.step m.program))^[n] (some c) = some d at h
  induction n generalizing d with
  | zero => have hd := Option.some.inj h; subst d; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (TM2.step m.program))^[n] (some c) with
    | none => simp [hp] at h
    | some prev =>
      have hs : TM2.step m.program prev = some d := by simpa only [hp, Option.bind_some] using h
      rw [Function.iterate_succ_apply',ih prev hp]
      rcases prev with ⟨label,state,tapes⟩
      cases label with
      | none => simp [TM2.step] at hs
      | some l =>
        have hd : TM2.stepAux (m.program l) state tapes = d := Option.some.inj hs
        subst d
        simp only [Option.bind_some,embedCfg,Option.elim_some,ordinaryStep,agree,embed_stepAux]

end Holant.Complexity.OracleBatch
