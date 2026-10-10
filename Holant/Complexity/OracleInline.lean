import Holant.Complexity.OracleSubroutine
import Holant.Complexity.OracleStateRename
import Holant.Complexity.StackProtocol

/-!
# Explicit oracle-call inlining protocol

This compiler runs a genuine finite oracle submachine on a copied query, clears the
old caller answer, copies the submachine's clean output back, and clears its private
workspace. Every copying/clearing step is a binary-stack instruction. Caller query
and answer indices may coincide: the query is copied before the answer is erased.
-/

namespace Holant.Complexity.OracleInline

open Turing StackProtocol

variable {J R τ : Type} [DecidableEq J] [Fintype J] [Fintype R] [Fintype τ]

abbrev Tape (m : OracleMachine) (J : Type) := m.K ⊕ (J ⊕ Unit)
abbrev Label (m : OracleMachine) (R : Type) := m.Λ ⊕ (Fin 8 ⊕ R)
abbrev State (m : OracleMachine) (τ : Type) := Option Bool × (m.σ × τ)

def stateEquiv (m : OracleMachine) (τ : Type) :
    (m.σ × (Option Bool × τ)) ≃ State m τ where
  toFun v := (v.2.1, (v.1, v.2.2))
  invFun v := (v.2.1, (v.1, v.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Eight protocol labels suffice for two copy loops, two clears, entry and return. -/
def phase (m : OracleMachine) (R : Type) (p : Fin 8) : Label m R := .inr (.inl p)

def callerTape (m : OracleMachine) (j : J) : Tape m J := .inr (.inl j)
def temporary (m : OracleMachine) (J : Type) : Tape m J := .inr (.inr ())

/-- Only finite-state rearrangements and stack primitives occur in the protocol. -/
def protocol (m : OracleMachine) (query answer : J) (ret : τ → R)
    (p : Fin 8) : TM2.Stmt (fun _ : Tape m J => Bool) (Label m R) (State m τ) :=
  if p = 0 then copyMoveStmt (callerTape m query) (temporary m J) (phase m R 0) (phase m R 1)
  else if p = 1 then copyRestoreStmt (callerTape m query) (.inl m.inputStack)
    (temporary m J) (phase m R 1) (phase m R 2)
  else if p = 2 then .load (fun v => (none, (m.initialState, v.2.2))) (.goto (fun _ => .inl m.main))
  else if p = 3 then clearStmt (callerTape m answer) (phase m R 3) (phase m R 4)
  else if p = 4 then copyMoveStmt (.inl m.outputStack) (temporary m J) (phase m R 4) (phase m R 5)
  else if p = 5 then copyRestoreStmt (.inl m.outputStack) (callerTape m answer)
    (temporary m J) (phase m R 5) (phase m R 6)
  else if p = 6 then clearStmt (.inl m.outputStack) (phase m R 6) (phase m R 7)
  else .goto (fun v => .inr (.inr (ret v.2.2)))

/-- The raw layout is chosen to apply the frame-preserving subroutine theorem. -/
abbrev rawMachine (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ)) : OracleMachine :=
  OracleSubroutine.machine m (none, initialMemory) (fun _ => Sum.inl (3 : Fin 8))
    (fun l => OracleStateRename.command (stateEquiv m τ).symm
      (match l with
       | .inl p => .ordinary (protocol m query answer ret p)
       | .inr r => outside r))

/-- A finite machine, with actual external oracle calls only inside the callee. -/
abbrev machine (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ)) : OracleMachine :=
  { OracleStateRename.machine (rawMachine m query answer initialMemory ret outside) (stateEquiv m τ) with
    inputStack := callerTape m query
    outputStack := callerTape m answer
    main := phase m R 0 }

def tapes (m : OracleMachine) (callee : m.K → List Bool) (frame : J → List Bool) :
    Tape m J → List Bool := Sum.elim callee (Sum.elim frame (fun _ => []))

omit [DecidableEq J] [Fintype J] in
@[simp] theorem tapes_caller (m : OracleMachine) (callee : m.K → List Bool) (frame : J → List Bool) (j : J) :
    tapes m callee frame (callerTape m j) = frame j := rfl

omit [DecidableEq J] [Fintype J] in
@[simp] theorem tapes_inner (m : OracleMachine) (callee : m.K → List Bool) (frame : J → List Bool) (k : m.K) :
    tapes m callee frame (.inl k) = callee k := rfl

omit [DecidableEq J] [Fintype J] in
@[simp] theorem tapes_temporary (m : OracleMachine) (callee : m.K → List Bool) (frame : J → List Bool) :
    tapes m callee frame (temporary m J) = [] := rfl

omit [Fintype J] in
theorem update_callee (m : OracleMachine) (callee : m.K → List Bool) (frame : J → List Bool)
    (k : m.K) (word : List Bool) :
    Function.update (tapes m callee frame) (.inl k) word =
      tapes m (Function.update callee k word) frame :=
  MachineFrame.update_left callee (Sum.elim frame (fun _ : Unit => [])) k word

omit [Fintype J] in
theorem update_caller (m : OracleMachine) (callee : m.K → List Bool) (frame : J → List Bool)
    (j : J) (word : List Bool) :
    Function.update (tapes m callee frame) (callerTape m j) word =
      tapes m callee (Function.update frame j word) := by
  funext k
  rcases k with k | j'
  · rfl
  · rcases j' with j' | u
    · simp only [Function.update_apply, callerTape, Sum.inr.injEq, Sum.inl.injEq,
        tapes, Sum.elim_inl, Sum.elim_inr]
    · rfl

/-- Start/end protocol configurations keep every caller tape explicit. -/
def cfg (m : OracleMachine) (label : Label m R) (memory : τ)
    (callee : m.K → List Bool) (frame : J → List Bool) :
    TM2.Cfg (fun _ : Tape m J => Bool) (Label m R) (State m τ) where
  l := some label
  var := (none, (m.initialState, memory))
  stk := tapes m callee frame

/-- Source configurations include the caller's unchanged words and empty temporary. -/
def calleeCfg (m : OracleMachine) (c : m.Cfg) (memory : τ) (frame : J → List Bool) :
    TM2.Cfg (fun _ : Tape m J => Bool) (Label m R) (State m τ) :=
  ⟨some (c.l.elim (phase m R 3) Sum.inl), (none, (c.var, memory)),
    Sum.elim c.stk (Sum.elim frame (fun _ : Unit => []))⟩

/-- The callee's real execution lifts with exactly the same transition bound. -/
def callee_correct (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (input output : List Bool) (time : ℕ)
    (memory : τ) (frame : J → List Bool)
    (h : m.OutputsInTime oracle input output time) :
    StateTransition.EvalsToInTime ((machine m query answer initialMemory ret outside).step oracle)
      (calleeCfg m (m.init input) memory frame) (some (calleeCfg m (m.output output) memory frame)) time := by
  have result := OracleStateRename.liftTimed (rawMachine m query answer initialMemory ret outside)
    (stateEquiv m τ) oracle _ _ time
    (OracleSubroutine.liftTimed m (none, initialMemory)
      (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
      (fun l => OracleStateRename.command (stateEquiv m τ).symm
        (match l with
         | .inl p => .ordinary (protocol m query answer ret p)
         | .inr r => outside r))
      oracle _ _ time (none, memory) (Sum.elim frame (fun _ : Unit => [])) h)
  have hs : (machine m query answer initialMemory ret outside).step oracle =
      (OracleStateRename.machine (rawMachine m query answer initialMemory ret outside) (stateEquiv m τ)).step oracle := by
    funext c
    rcases c with ⟨label, state, data⟩
    cases label with
    | none => rfl
    | some label =>
      simp only [OracleMachine.step, machine]
      cases hc : (OracleStateRename.machine (rawMachine m query answer initialMemory ret outside)
        (stateEquiv m τ)).program label <;> simp_all only
  rw [hs]
  simpa only [OracleStateRename.cfg, MachineReturn.cfg, calleeCfg, stateEquiv, phase,
    OracleMachine.init, OracleMachine.output, Option.elim_some, Option.elim_none, Equiv.coe_fn_mk] using result

/-- Protocol labels execute the specified finite binary-stack statement. -/
theorem executes_protocol (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (p : Fin 8) :
    ExecutesAt ((machine m query answer initialMemory ret outside).step oracle)
      (phase m R p) (protocol m query answer ret p) := by
  intro state tapes
  simp only [machine, rawMachine, OracleStateRename.machine, OracleSubroutine.machine,
    OracleMachine.step, phase, OracleStateRename.command]
  have hh := MachineRename.stmt_state_inverse (stateEquiv m τ).symm (protocol m query answer ret p)
  simp only [Equiv.symm_symm] at hh
  rw [hh]

/-- Copy the query into a clean private workspace, then enter the callee. -/
def prepare_correct (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (memory : τ) (frame : J → List Bool) :
    StateTransition.EvalsToInTime ((machine m query answer initialMemory ret outside).step oracle)
      (cfg m (phase m R 0) memory (fun _ => []) frame)
      (some (calleeCfg m (m.init (frame query)) memory frame)) (2 * ((frame query).length + 1) + 1) := by
  let step := (machine m query answer initialMemory ret outside).step oracle
  have hp := executes_protocol m query answer initialMemory ret outside oracle
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
      (cfg m (phase m R 0) memory (fun _ => []) frame)
      (some (cfg m (phase m R 2) memory (m.init (frame query)).stk frame))
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
  have he : step (cfg m (phase m R 2) memory (m.init (frame query)).stk frame) =
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
def finish_correct (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (memory : τ) (frame : J → List Bool) (value : List Bool) :
    StateTransition.EvalsToInTime ((machine m query answer initialMemory ret outside).step oracle)
      (calleeCfg m (m.output value) memory frame)
      (some (cfg m (.inr (.inr (ret memory))) memory (fun _ => []) (Function.update frame answer value)))
      ((frame answer).length + 1 + 2 * (value.length + 1) + (value.length + 1) + 1) := by
  let step := (machine m query answer initialMemory ret outside).step oracle
  have hp := executes_protocol m query answer initialMemory ret outside oracle
  let outputTapes := (m.output value).stk
  have hc := clear_correct step (callerTape m answer) (phase m R 3) (phase m R 4)
    (by simpa [protocol, step] using hp 3) (m.initialState, memory) (tapes m outputTapes frame)
  have hc' : StateTransition.EvalsToInTime step (calleeCfg m (m.output value) memory frame)
      (some (cfg m (phase m R 4) memory outputTapes (Function.update frame answer [])))
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
      (cfg m (phase m R 4) memory outputTapes (Function.update frame answer []))
      (some (cfg m (phase m R 6) memory outputTapes (Function.update frame answer value)))
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
      (cfg m (phase m R 6) memory outputTapes (Function.update frame answer value))
      (some (cfg m (phase m R 7) memory (fun _ => []) (Function.update frame answer value)))
      (value.length + 1) := hclean
  have hreturn : step (cfg m (phase m R 7) memory (fun _ => []) (Function.update frame answer value)) =
      some (cfg m (.inr (.inr (ret memory))) memory (fun _ => []) (Function.update frame answer value)) := by
    calc
      _ = some (TM2.stepAux (protocol m query answer ret 7) (none, (m.initialState, memory))
          (tapes m (fun _ => []) (Function.update frame answer value))) := hp 7 _ _
      _ = _ := by simp [protocol, TM2.stepAux, cfg]
  have h1 := StateTransition.EvalsToInTime.trans step ((frame answer).length + 1)
    (2 * (value.length + 1)) _ _ _ hc' hcopy'
  have h2 := StateTransition.EvalsToInTime.trans step
    (2 * (value.length + 1) + ((frame answer).length + 1)) (value.length + 1) _ _ _ h1 hclean'
  have h3 := StateTransition.EvalsToInTime.trans step
    ((value.length + 1) + (2 * (value.length + 1) + ((frame answer).length + 1))) 1 _ _ _ h2
    (runsExactly_one hreturn).toTimed
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h3

/-- A complete real oracle-call simulation, charging for input/output words and
replacement of the previous answer, including the aliased query/answer case. -/
def call_correct (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (memory : τ) (frame : J → List Bool)
    (value : List Bool) (time : ℕ) (h : m.OutputsInTime oracle (frame query) value time) :
    StateTransition.EvalsToInTime ((machine m query answer initialMemory ret outside).step oracle)
      (cfg m (phase m R 0) memory (fun _ => []) frame)
      (some (cfg m (.inr (.inr (ret memory))) memory (fun _ => []) (Function.update frame answer value)))
      (time + 2 * (frame query).length + (frame answer).length + 3 * value.length + 8) := by
  let step := (machine m query answer initialMemory ret outside).step oracle
  have h1 := prepare_correct m query answer initialMemory ret outside oracle memory frame
  have h2 := callee_correct m query answer initialMemory ret outside oracle (frame query) value time memory frame h
  have h3 := finish_correct m query answer initialMemory ret outside oracle memory frame value
  have h12 := StateTransition.EvalsToInTime.trans step (2 * ((frame query).length + 1) + 1)
    time _ _ _ h1 h2
  have h123 := StateTransition.EvalsToInTime.trans step (time + (2 * ((frame query).length + 1) + 1))
    ((frame answer).length + 1 + 2 * (value.length + 1) + (value.length + 1) + 1) _ _ _ h12 h3
  convert h123 using 1
  omega

/-- Caller commands retain their literal instruction syntax after state conversion. -/
theorem program_outside (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ)) (r : R) :
    (machine m query answer initialMemory ret outside).program (.inr (.inr r)) = outside r := by
  cases h : outside r with
  | ordinary q =>
    simp only [machine, rawMachine, OracleStateRename.machine, OracleSubroutine.machine,
      OracleStateRename.command, h]
    have hh := MachineRename.stmt_state_inverse (stateEquiv m τ).symm q
    simpa only [Equiv.symm_symm] using congrArg OracleCommand.ordinary hh
  | query next =>
    simp [machine, rawMachine, OracleStateRename.machine, OracleSubroutine.machine,
      OracleStateRename.command, h]

omit [DecidableEq J] [Fintype J] [Fintype R] [Fintype τ] in
/-- At most six primitive binary-stack instructions occur in one protocol step. -/
theorem protocol_budget_le (m : OracleMachine) (query answer : J) (ret : τ → R) (p : Fin 8) :
    TM2Cost.budget (protocol m query answer ret p) ≤ 6 := by
  unfold protocol
  split_ifs <;> simp [TM2Cost.budget]

end Holant.Complexity.OracleInline
