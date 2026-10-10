import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Complexity.OracleCompose

/-! Ported proof; verification is recorded in the task build logs. Execution receipts for the EXISTING OracleInline
protocol. No opcode, machine, forest or query algorithm is replaced.
prepare/finish are proved ordinary executions of the same copy/clear
statements. The callee lift preserves the exact external-query word list.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal
open Computability Holant.Complexity Turing
open OracleInline StackProtocol OracleBatch
set_option backward.isDefEq.respectTransparency false
variable {J R τ : Type} [DecidableEq J] [Fintype J] [Fintype R] [Fintype τ]

/-- Literal protocol command, before execution or any oracle is chosen. -/
theorem protocol_command (m : OracleMachine) (query answer : J) (initial : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ)) (p : Fin 8) :
    (OracleInline.machine m query answer initial ret outside).program (phase m R p) =
      .ordinary (OracleInline.protocol m query answer ret p) := by
  simp only [OracleInline.machine,rawMachine,OracleStateRename.machine,OracleSubroutine.machine,
    phase,OracleStateRename.command]
  have hh := MachineRename.stmt_state_inverse (stateEquiv m τ).symm (OracleInline.protocol m query answer ret p)
  simp only [Equiv.symm_symm] at hh
  exact congrArg OracleCommand.ordinary hh

theorem protocol_ordinary (m : OracleMachine) (query answer : J) (initial : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ)) (p : Fin 8) :
    ExecutesAt (ordinaryStep (OracleInline.machine m query answer initial ret outside))
      (phase m R p) (OracleInline.protocol m query answer ret p) := by
  intro state tapes
  simp only [OracleInline.machine,rawMachine,OracleStateRename.machine,OracleSubroutine.machine,
    ordinaryStep,phase,OracleStateRename.command]
  have hh := MachineRename.stmt_state_inverse (stateEquiv m τ).symm (OracleInline.protocol m query answer ret p)
  simp only [Equiv.symm_symm] at hh
  rw [hh]

/-- This uses exactly the old prepare copy loops and entry load. Erasing
queries is a proof relation only; it is not a new implementation. -/
def prepare_ordinary (m : OracleMachine) (query answer : J) (initial : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (memory : τ) (frame : J → List Bool) :
    StateTransition.EvalsToInTime (ordinaryStep (OracleInline.machine m query answer initial ret outside))
      (OracleInline.cfg m (phase m R 0) memory (fun _ => []) frame)
      (some (calleeCfg m (m.init (frame query)) memory frame))
      (2 * ((frame query).length + 1) + 1) := by
  let step := ordinaryStep (OracleInline.machine m query answer initial ret outside)
  have hp := protocol_ordinary m query answer initial ret outside
  have hm : ExecutesAt step (phase m R 0)
      (copyMoveStmt (callerTape m query) (temporary m J) (phase m R 0) (phase m R 1)) := by
    simpa [OracleInline.protocol,step] using hp 0
  have hr : ExecutesAt step (phase m R 1)
      (copyRestoreStmt (callerTape m query) (.inl m.inputStack)
        (temporary m J) (phase m R 1) (phase m R 2)) := by
    simpa [OracleInline.protocol,step] using hp 1
  have hc := copy_correct (callerTape m query) (.inl m.inputStack) (temporary m J)
    (by simp [callerTape]) (by simp [callerTape,temporary]) (by simp [temporary])
    step (phase m R 0) (phase m R 1) (phase m R 2) hm hr
    (m.initialState,memory) (OracleInline.tapes m (fun _ => []) frame) rfl
  have hi : Function.update (fun _ : m.K => ([] : List Bool)) m.inputStack (frame query) =
      (m.init (frame query)).stk := by
    funext k
    simp [OracleMachine.init,Function.update]
  have hc' : StateTransition.EvalsToInTime step
      (OracleInline.cfg m (phase m R 0) memory (fun _ => []) frame)
      (some (OracleInline.cfg m (phase m R 2) memory (m.init (frame query)).stk frame))
      (2 * ((frame query).length + 1)) := by
    change StateTransition.EvalsToInTime step
      (StackProtocol.cfg (phase m R 0) (m.initialState,memory) (OracleInline.tapes m (fun _ => []) frame))
      (some (StackProtocol.cfg (phase m R 2) (m.initialState,memory)
        (OracleInline.tapes m (m.init (frame query)).stk frame))) _
    change StateTransition.EvalsToInTime step _
      (some (StackProtocol.cfg (phase m R 2) (m.initialState,memory)
        (Function.update (OracleInline.tapes m (fun _ => []) frame) (.inl m.inputStack)
          (frame query ++ [])))) (2 * ((frame query).length + 1)) at hc
    simpa only [List.append_nil,update_callee,hi] using hc
  have he : step (OracleInline.cfg m (phase m R 2) memory (m.init (frame query)).stk frame) =
      some (calleeCfg m (m.init (frame query)) memory frame) := by
    change step (StackProtocol.cfg (phase m R 2) (m.initialState,memory)
      (OracleInline.tapes m (m.init (frame query)).stk frame)) = _
    calc
      _ = some (TM2.stepAux (OracleInline.protocol m query answer ret 2) (none,(m.initialState,memory))
          (OracleInline.tapes m (m.init (frame query)).stk frame)) := hp 2 _ _
      _ = _ := by simp [OracleInline.protocol,TM2.stepAux,calleeCfg,OracleMachine.init,OracleInline.tapes]
  have ht := StateTransition.EvalsToInTime.trans step (2 * ((frame query).length + 1)) 1
    _ _ _ hc' (runsExactly_one he).toTimed
  simpa only [Nat.add_comm] using ht

/-- Same old clear/copy/clear/return instructions, with no external query
at any prefix of this execution. Query and answer stacks may be aliased. -/
def finish_ordinary (m : OracleMachine) (query answer : J) (initial : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (memory : τ) (frame : J → List Bool) (value : List Bool) :
    StateTransition.EvalsToInTime (ordinaryStep (OracleInline.machine m query answer initial ret outside))
      (calleeCfg m (m.output value) memory frame)
      (some (OracleInline.cfg m (.inr (.inr (ret memory))) memory (fun _ => [])
        (Function.update frame answer value)))
      ((frame answer).length + 1 + 2 * (value.length + 1) + (value.length + 1) + 1) := by
  let step := ordinaryStep (OracleInline.machine m query answer initial ret outside)
  have hp := protocol_ordinary m query answer initial ret outside
  let outputTapes := (m.output value).stk
  have hc := clear_correct step (callerTape m answer) (phase m R 3) (phase m R 4)
    (by simpa [OracleInline.protocol,step] using hp 3) (m.initialState,memory) (OracleInline.tapes m outputTapes frame)
  have hc' : StateTransition.EvalsToInTime step (calleeCfg m (m.output value) memory frame)
      (some (OracleInline.cfg m (phase m R 4) memory outputTapes (Function.update frame answer [])))
      ((frame answer).length + 1) := by
    change StateTransition.EvalsToInTime step _
      (some (StackProtocol.cfg (phase m R 4) (m.initialState,memory)
        (Function.update (OracleInline.tapes m outputTapes frame) (callerTape m answer) [])))
      ((frame answer).length + 1) at hc
    rw [update_caller] at hc
    exact hc
  have hcopy := copy_correct (.inl m.outputStack) (callerTape m answer) (temporary m J)
    (by simp [callerTape]) (by simp [temporary]) (by simp [callerTape,temporary])
    step (phase m R 4) (phase m R 5) (phase m R 6)
    (by simpa [OracleInline.protocol,step] using hp 4) (by simpa [OracleInline.protocol,step] using hp 5)
    (m.initialState,memory) (OracleInline.tapes m outputTapes (Function.update frame answer [])) rfl
  have ho : OracleInline.tapes m outputTapes (Function.update frame answer []) (.inl m.outputStack) = value := by
    simp only [OracleInline.tapes,Sum.elim_inl,outputTapes,OracleMachine.output,ite_true]
  have ha : OracleInline.tapes m outputTapes (Function.update frame answer []) (callerTape m answer) = [] := by
    simp only [OracleInline.tapes,callerTape,Sum.elim_inr,Sum.elim_inl,Function.update_self]
  rw [ho,ha,List.append_nil,update_caller,Function.update_idem] at hcopy
  have hcopy' : StateTransition.EvalsToInTime step
      (OracleInline.cfg m (phase m R 4) memory outputTapes (Function.update frame answer []))
      (some (OracleInline.cfg m (phase m R 6) memory outputTapes (Function.update frame answer value)))
      (2 * (value.length + 1)) := hcopy
  have hclean := clear_correct step (.inl m.outputStack) (phase m R 6) (phase m R 7)
    (by simpa [OracleInline.protocol,step] using hp 6) (m.initialState,memory)
    (OracleInline.tapes m outputTapes (Function.update frame answer value))
  have ho' : OracleInline.tapes m outputTapes (Function.update frame answer value) (.inl m.outputStack) = value := by
    simp only [OracleInline.tapes,Sum.elim_inl,outputTapes,OracleMachine.output,ite_true]
  have he : Function.update outputTapes m.outputStack [] = (fun _ => []) := by
    funext k
    by_cases h : k = m.outputStack <;> simp [outputTapes,OracleMachine.output,Function.update,h]
  rw [ho',update_callee,he] at hclean
  have hclean' : StateTransition.EvalsToInTime step
      (OracleInline.cfg m (phase m R 6) memory outputTapes (Function.update frame answer value))
      (some (OracleInline.cfg m (phase m R 7) memory (fun _ => []) (Function.update frame answer value)))
      (value.length + 1) := hclean
  have hreturn : step (OracleInline.cfg m (phase m R 7) memory (fun _ => [])
      (Function.update frame answer value)) =
      some (OracleInline.cfg m (.inr (.inr (ret memory))) memory (fun _ => [])
        (Function.update frame answer value)) := by
    calc
      _ = some (TM2.stepAux (OracleInline.protocol m query answer ret 7) (none,(m.initialState,memory))
          (OracleInline.tapes m (fun _ => []) (Function.update frame answer value))) := hp 7 _ _
      _ = _ := by simp [OracleInline.protocol,TM2.stepAux,OracleInline.cfg]
  have h1 := StateTransition.EvalsToInTime.trans step ((frame answer).length + 1)
    (2 * (value.length + 1)) _ _ _ hc' hcopy'
  have h2 := StateTransition.EvalsToInTime.trans step
    (2 * (value.length + 1) + ((frame answer).length + 1)) (value.length + 1) _ _ _ h1 hclean'
  have h3 := StateTransition.EvalsToInTime.trans step
    ((value.length + 1) + (2 * (value.length + 1) + ((frame answer).length + 1))) 1 _ _ _ h2
    (runsExactly_one hreturn).toTimed
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h3

/-- Exact one-step receipt through the existing subroutine + state rename.
It applies only to a successful real callee transition. -/
theorem callee_step (m : OracleMachine) (query answer : J) (initial : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (c d : m.Cfg) (memory : τ) (frame : J → List Bool)
    (h : m.step oracle c = some d) :
    (OracleInline.machine m query answer initial ret outside).step oracle (calleeCfg m c memory frame) =
      some (calleeCfg m d memory frame) := by
  let raw := rawMachine m query answer initial ret outside
  let lifted := MachineReturn.cfg
    (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
    c (none,memory) (Sum.elim frame (fun _ : Unit => []))
  have hs := OracleSubroutine.step_of_step m (none,initial)
    (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
    (fun l => OracleStateRename.command (stateEquiv m τ).symm
      (match l with
       | .inl p => .ordinary (OracleInline.protocol m query answer ret p)
       | .inr r => outside r))
    oracle c d (none,memory) (Sum.elim frame (fun _ : Unit => [])) h
  have hr := OracleStateRename.step raw (stateEquiv m τ) oracle lifted
  change (OracleStateRename.machine raw (stateEquiv m τ)).step oracle
      (OracleStateRename.cfg raw (stateEquiv m τ) lifted) =
      (raw.step oracle lifted).map (OracleStateRename.cfg raw (stateEquiv m τ)) at hr
  rw [show raw.step oracle lifted = some (MachineReturn.cfg
    (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
    d (none,memory) (Sum.elim frame (fun _ : Unit => []))) from hs] at hr
  have he : (OracleInline.machine m query answer initial ret outside).step oracle =
      (OracleStateRename.machine raw (stateEquiv m τ)).step oracle := by
    funext c
    rcases c with ⟨label,state,data⟩
    cases label with
    | none => rfl
    | some label =>
      simp only [OracleMachine.step,OracleInline.machine]
      cases hc : (OracleStateRename.machine raw (stateEquiv m τ)).program label <;> simp_all only [raw]
  rw [he]
  simpa only [raw,lifted,OracleStateRename.cfg,MachineReturn.cfg,
    calleeCfg,stateEquiv,phase,Equiv.coe_fn_mk,Option.map_some] using hr

theorem callee_words (m : OracleMachine) (query answer : J) (initial : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (c : m.Cfg) (memory : τ) (frame : J → List Bool) :
    queryWords (OracleInline.machine m query answer initial ret outside) (calleeCfg m c memory frame) =
      queryWords m c := by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => simp only [queryWords,calleeCfg,Option.elim_none,OracleInline.machine,
      rawMachine,OracleStateRename.machine,OracleSubroutine.machine,phase,
      OracleStateRename.command]
  | some label =>
      cases hp : m.program label <;>
        simp [queryWords,calleeCfg,OracleInline.machine,rawMachine,OracleStateRename.machine,
          OracleSubroutine.machine,OracleStateRename.command,hp]

/-- All query words are lifted literally, with their order and repetitions.
The successful-endpoint hypothesis is just the actual callee execution. -/
theorem callee_trace (m : OracleMachine) (query answer : J) (initial : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (c d : m.Cfg) (memory : τ) (frame : J → List Bool)
    (n : ℕ) (h : (fun p => p.bind (m.step oracle))^[n] (some c) = some d) :
    RunsTrace (OracleInline.machine m query answer initial ret outside) oracle
      (calleeCfg m c memory frame) (calleeCfg m d memory frame) n (queryTrace m oracle c n) := by
  induction n generalizing c with
  | zero =>
      have same := Option.some.inj h
      subst d
      exact ⟨rfl,rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      cases hs : m.step oracle c with
      | none => simp [hs] at h
      | some e =>
          have ht : (fun p => p.bind (m.step oracle))^[n] (some e) = some d := by
            simpa only [Option.bind_some,hs] using h
          have tail := ih e ht
          have first := callee_step m query answer initial ret outside oracle c e memory frame hs
          constructor
          · simpa only [Function.iterate_succ_apply,Option.bind_some,first] using tail.run
          · simpa only [queryTrace,first,hs,callee_words] using
              congrArg (fun words => queryWords m c ++ words) tail.trace

end Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal
