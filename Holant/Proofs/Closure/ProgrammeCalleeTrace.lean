import Holant.Proofs.Closure.PhysicalTrace
import Holant.Proofs.Closure.ProgrammeProtocol
import Holant.Complexity.OracleMetadata

/-! Reconstructed exact callee simulation and ordered transcript preservation.
The frozen subroutine/state-renaming compilers supply the actual transition;
the source run's Some endpoint excludes premature return-protocol execution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeCalleeTrace
open Holant.Complexity Turing OracleInline
variable {J R τ : Type} [DecidableEq J] [Fintype J] [Fintype R] [Fintype τ]

private theorem machine_step (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) :
    (machine m query answer initialMemory ret outside).step oracle =
      (OracleStateRename.machine (rawMachine m query answer initialMemory ret outside) (stateEquiv m τ)).step oracle :=
  OracleMachine.step_withEntry _ _ _ _ _

/-- One genuine source step preserves every caller tape and memory cell. -/
theorem callee_step (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (c d : m.Cfg) (memory : τ) (frame : J → List Bool)
    (h : m.step oracle c = some d) :
    (machine m query answer initialMemory ret outside).step oracle (calleeCfg m c memory frame) =
      some (calleeCfg m d memory frame) := by
  have raw := OracleSubroutine.step_of_step m (none,initialMemory)
    (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
    (fun l => OracleStateRename.command (stateEquiv m τ).symm
      (match l with
      | .inl p => .ordinary (protocol m query answer ret p)
      | .inr r => outside r))
    oracle c d (none,memory) (Sum.elim frame (fun _ : Unit => [])) h
  have rawStep : (rawMachine m query answer initialMemory ret outside).step oracle
      (MachineReturn.cfg (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
        c (none,memory) (Sum.elim frame (fun _ : Unit => []))) =
      some (MachineReturn.cfg (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
        d (none,memory) (Sum.elim frame (fun _ : Unit => []))) := raw
  have renamed := OracleStateRename.step (rawMachine m query answer initialMemory ret outside)
    (stateEquiv m τ) oracle
    (MachineReturn.cfg (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
      c (none,memory) (Sum.elim frame (fun _ : Unit => [])))
  rw [rawStep] at renamed
  rw [machine_step]
  simpa only [OracleStateRename.cfg,MachineReturn.cfg,calleeCfg,stateEquiv,phase,
    Equiv.coe_fn_mk,Option.map_some] using renamed

/-- The actual iterate preserves the exact source transition count. -/
theorem callee_run (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (c d : m.Cfg) (memory : τ) (frame : J → List Bool)
    (t : ℕ) (h : (fun p => p.bind (m.step oracle))^[t] (some c) = some d) :
    (fun p => p.bind ((machine m query answer initialMemory ret outside).step oracle))^[t]
      (some (calleeCfg m c memory frame)) = some (calleeCfg m d memory frame) := by
  induction t generalizing d with
  | zero => have hd := Option.some.inj h; subst d; rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (m.step oracle))^[t] (some c) with
    | none => simp [hp] at h
    | some previous =>
      have hs : m.step oracle previous = some d := by simpa [hp] using h
      rw [Function.iterate_succ_apply',ih previous hp]
      exact callee_step m query answer initialMemory ret outside oracle previous d memory frame hs

/-- Exact words are unchanged; a clean source halt enters ordinary phase 3. -/
theorem callee_words (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (c : m.Cfg) (memory : τ) (frame : J → List Bool) :
    OracleBatch.queryWords (machine m query answer initialMemory ret outside) (calleeCfg m c memory frame) =
      OracleBatch.queryWords m c := by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none =>
    simp [OracleBatch.queryWords,machine,rawMachine,OracleStateRename.machine,
      OracleSubroutine.machine,OracleStateRename.command,calleeCfg,phase]
  | some label =>
    cases hp : m.program label <;>
      simp [OracleBatch.queryWords,machine,rawMachine,OracleStateRename.machine,
        OracleSubroutine.machine,OracleStateRename.command,calleeCfg,phase,hp]

/-- This is LIST equality of the same execution, including repeated queries. -/
theorem callee_trace (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (c d : m.Cfg) (memory : τ) (frame : J → List Bool)
    (t : ℕ) (h : (fun p => p.bind (m.step oracle))^[t] (some c) = some d) :
    OracleBatch.queryTrace (machine m query answer initialMemory ret outside) oracle
      (calleeCfg m c memory frame) t = OracleBatch.queryTrace m oracle c t := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : m.step oracle c with
    | none => simp [hs] at h
    | some next =>
      have rest : (fun p => p.bind (m.step oracle))^[t] (some next) = some d := by
        simpa only [Option.bind_some,hs] using h
      have step := callee_step m query answer initialMemory ret outside oracle c next memory frame hs
      simp only [OracleBatch.queryTrace,step,hs,
        callee_words m query answer initialMemory ret outside c memory frame,ih next rest]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeCalleeTrace
