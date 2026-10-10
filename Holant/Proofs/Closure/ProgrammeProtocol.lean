import Holant.Complexity.OracleInline
import Holant.Complexity.OracleBatch.QueryTrace

/-! Reconstructed from the frozen actual copy/clear protocol. The SAME literal
instructions are replayed with oracle transitions erased, proving that prepare
and finish contain no external queries and retain their true word-length clocks. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeProtocol
open Holant.Complexity Turing StackProtocol OracleInline
variable {J R τ : Type} [DecidableEq J] [Fintype J] [Fintype R] [Fintype τ]

theorem executes_protocol_ordinary (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (p : Fin 8) :
    ExecutesAt (OracleBatch.ordinaryStep (machine m query answer initialMemory ret outside))
      (phase m R p) (protocol m query answer ret p) := by
  intro state tapes
  simp only [machine, rawMachine, OracleStateRename.machine, OracleSubroutine.machine,
    OracleBatch.ordinaryStep, phase, OracleStateRename.command]
  have hh := MachineRename.stmt_state_inverse (stateEquiv m τ).symm (protocol m query answer ret p)
  simp only [Equiv.symm_symm] at hh
  rw [hh]

/-- Copy the query into a clean private workspace, then enter the callee. -/
def prepare_ordinary (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (memory : τ) (frame : J → List Bool) :
    StateTransition.EvalsToInTime (OracleBatch.ordinaryStep (machine m query answer initialMemory ret outside))
      (OracleInline.cfg m (phase m R 0) memory (fun _ => []) frame)
      (some (calleeCfg m (m.init (frame query)) memory frame)) (2 * ((frame query).length + 1) + 1) := by
  let step := OracleBatch.ordinaryStep (machine m query answer initialMemory ret outside)
  have hp := executes_protocol_ordinary m query answer initialMemory ret outside oracle
  have hm : ExecutesAt step (phase m R 0)
      (copyMoveStmt (callerTape m query) (temporary m J) (phase m R 0) (phase m R 1)) := by
    simpa [protocol, step] using hp 0
  have hr : ExecutesAt step (phase m R 1)
      (copyRestoreStmt (callerTape m query) (.inl m.inputStack) (temporary m J)
        (phase m R 1) (phase m R 2)) := by
    simpa [protocol, step] using hp 1
  have hc := copy_correct (callerTape m query) (.inl m.inputStack) (temporary m J)
    (by simp [callerTape]) (by simp [callerTape, temporary]) (by simp [temporary])
    step (phase m R 0) (phase m R 1) (phase m R 2) hm hr
    (m.initialState, memory) (tapes m (fun _ => []) frame) rfl
  have hi : Function.update (fun _ : m.K => ([] : List Bool)) m.inputStack (frame query) =
      (m.init (frame query)).stk := by
    funext k; simp [OracleMachine.init, Function.update]
  have hc' : StateTransition.EvalsToInTime step
      (OracleInline.cfg m (phase m R 0) memory (fun _ => []) frame)
      (some (OracleInline.cfg m (phase m R 2) memory (m.init (frame query)).stk frame))
      (2 * ((frame query).length + 1)) := by
    change StateTransition.EvalsToInTime step
      (StackProtocol.cfg (phase m R 0) (m.initialState, memory) (tapes m (fun _ => []) frame))
      (some (StackProtocol.cfg (phase m R 2) (m.initialState, memory)
        (tapes m (m.init (frame query)).stk frame))) _
    change StateTransition.EvalsToInTime step _
      (some (StackProtocol.cfg (phase m R 2) (m.initialState, memory)
        (Function.update (tapes m (fun _ => []) frame) (.inl m.inputStack)
          (frame query ++ [])))) (2 * ((frame query).length + 1)) at hc
    simpa only [List.append_nil, update_callee, hi] using hc
  have he : step (OracleInline.cfg m (phase m R 2) memory (m.init (frame query)).stk frame) =
      some (calleeCfg m (m.init (frame query)) memory frame) := by
    change step (StackProtocol.cfg (phase m R 2) (m.initialState, memory)
      (tapes m (m.init (frame query)).stk frame)) = _
    calc
      _ = some (TM2.stepAux (protocol m query answer ret 2) (none, (m.initialState, memory))
          (tapes m (m.init (frame query)).stk frame)) := hp 2 _ _
      _ = _ := by simp [protocol, TM2.stepAux, calleeCfg, OracleMachine.init, tapes]
  have ht := StateTransition.EvalsToInTime.trans step (2 * ((frame query).length + 1)) 1
    _ _ _ hc' (runsExactly_one he).toTimed
  simpa only [Nat.add_comm] using ht

/-- Install the result and clear every private tape before returning to caller control. -/
def finish_ordinary (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (memory : τ) (frame : J → List Bool) (value : List Bool) :
    StateTransition.EvalsToInTime (OracleBatch.ordinaryStep (machine m query answer initialMemory ret outside))
      (calleeCfg m (m.output value) memory frame)
      (some (OracleInline.cfg m (.inr (.inr (ret memory))) memory (fun _ => []) (Function.update frame answer value)))
      ((frame answer).length + 1 + 2 * (value.length + 1) + (value.length + 1) + 1) := by
  let step := OracleBatch.ordinaryStep (machine m query answer initialMemory ret outside)
  have hp := executes_protocol_ordinary m query answer initialMemory ret outside oracle
  let outputTapes := (m.output value).stk
  have hc := clear_correct step (callerTape m answer) (phase m R 3) (phase m R 4)
    (by simpa [protocol, step] using hp 3) (m.initialState, memory) (tapes m outputTapes frame)
  have hc' : StateTransition.EvalsToInTime step (calleeCfg m (m.output value) memory frame)
      (some (OracleInline.cfg m (phase m R 4) memory outputTapes (Function.update frame answer [])))
      ((frame answer).length + 1) := by
    change StateTransition.EvalsToInTime step _
      (some (StackProtocol.cfg (phase m R 4) (m.initialState, memory)
        (Function.update (tapes m outputTapes frame) (callerTape m answer) [])))
      ((frame answer).length + 1) at hc
    rw [update_caller] at hc
    exact hc
  have hcopy := copy_correct (.inl m.outputStack) (callerTape m answer) (temporary m J)
    (by simp [callerTape]) (by simp [temporary]) (by simp [callerTape, temporary])
    step (phase m R 4) (phase m R 5) (phase m R 6)
    (by simpa [protocol, step] using hp 4) (by simpa [protocol, step] using hp 5)
    (m.initialState, memory) (tapes m outputTapes (Function.update frame answer [])) rfl
  have ho : tapes m outputTapes (Function.update frame answer []) (.inl m.outputStack) = value := by
    simp only [tapes, Sum.elim_inl, outputTapes, OracleMachine.output, ite_true]
  have ha : tapes m outputTapes (Function.update frame answer []) (callerTape m answer) = [] := by
    simp only [tapes, callerTape, Sum.elim_inr, Sum.elim_inl, Function.update_self]
  rw [ho, ha, List.append_nil, update_caller, Function.update_idem] at hcopy
  have hcopy' : StateTransition.EvalsToInTime step
      (OracleInline.cfg m (phase m R 4) memory outputTapes (Function.update frame answer []))
      (some (OracleInline.cfg m (phase m R 6) memory outputTapes (Function.update frame answer value)))
      (2 * (value.length + 1)) := hcopy
  have hclean := clear_correct step (.inl m.outputStack) (phase m R 6) (phase m R 7)
    (by simpa [protocol, step] using hp 6) (m.initialState, memory)
    (tapes m outputTapes (Function.update frame answer value))
  have ho' : tapes m outputTapes (Function.update frame answer value) (.inl m.outputStack) = value := by
    simp only [tapes, Sum.elim_inl, outputTapes, OracleMachine.output, ite_true]
  have he : Function.update outputTapes m.outputStack [] = (fun _ => []) := by
    funext k
    by_cases h : k = m.outputStack <;> simp [outputTapes, OracleMachine.output, Function.update, h]
  rw [ho', update_callee, he] at hclean
  have hclean' : StateTransition.EvalsToInTime step
      (OracleInline.cfg m (phase m R 6) memory outputTapes (Function.update frame answer value))
      (some (OracleInline.cfg m (phase m R 7) memory (fun _ => []) (Function.update frame answer value)))
      (value.length + 1) := hclean
  have hreturn : step (OracleInline.cfg m (phase m R 7) memory (fun _ => []) (Function.update frame answer value)) =
      some (OracleInline.cfg m (.inr (.inr (ret memory))) memory (fun _ => []) (Function.update frame answer value)) := by
    calc
      _ = some (TM2.stepAux (protocol m query answer ret 7) (none, (m.initialState, memory))
          (tapes m (fun _ => []) (Function.update frame answer value))) := hp 7 _ _
      _ = _ := by simp [protocol, TM2.stepAux, OracleInline.cfg]
  have h1 := StateTransition.EvalsToInTime.trans step ((frame answer).length + 1)
    (2 * (value.length + 1)) _ _ _ hc' hcopy'
  have h2 := StateTransition.EvalsToInTime.trans step
    (2 * (value.length + 1) + ((frame answer).length + 1)) (value.length + 1) _ _ _ h1 hclean'
  have h3 := StateTransition.EvalsToInTime.trans step
    ((value.length + 1) + (2 * (value.length + 1) + ((frame answer).length + 1))) 1 _ _ _ h2
    (runsExactly_one hreturn).toTimed
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h3

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeProtocol
