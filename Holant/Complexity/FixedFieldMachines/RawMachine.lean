import Holant.Complexity.FixedFieldMachines.ExecutionView

/-! Executable finite-program projection without eager state/label enumeration.
The composition and returning-map constructors are proved equal to the same
programs as `BinaryCompose.Machine` constructors. Only unused enumeration
metadata is omitted. Stack-key enumeration is retained for complete cleanup tests. -/
namespace Holant.Complexity.FixedFieldMachines
open Turing BinaryCompose StackProtocol

structure RawMachine where
  K : Type
  [keyEq : DecidableEq K]
  [finiteK : Fintype K]
  input : K
  output : K
  Label : Type
  main : Label
  State : Type
  initial : State
  program : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] RawMachine.keyEq RawMachine.finiteK

namespace RawMachine

def erase (m : Machine) : RawMachine where
  K := m.K
  keyEq := m.decidableK
  finiteK := m.finiteK
  input := m.input
  output := m.output
  Label := m.Label
  main := m.main
  State := m.State
  initial := m.initial
  program := m.program

abbrev Config (m : RawMachine) := TM2.Cfg (fun _ : m.K => Bool) m.Label m.State

def view (m : RawMachine) : ExecutionView m.K m.Label m.State where
  keyEq := m.keyEq
  step := TM2.step m.program
  start word := ⟨some m.main, m.initial, wordTape m.input word⟩
  output := m.output
  keys := Finset.univ

@[simp] theorem view_erase_step (m : Machine) : (erase m).view.step = m.computer.step := rfl
@[simp] theorem view_erase_start (m : Machine) (word : List Bool) :
    (erase m).view.start word = initList m.computer word := (m.init_eq word).symm
@[simp] theorem view_erase_output (m : Machine) : (erase m).view.output = m.output := rfl
@[simp] theorem view_erase_keys (m : Machine) (k : m.K) : k ∈ (erase m).view.keys := Finset.mem_univ k

theorem view_erase_observer (m : Machine) (c : m.Config) :
    (erase m).view.observeHalt c =
      (c.stk m.output, decide (∀ k, k ≠ m.output → c.stk k = [])) := by
  simp only [view, erase, ExecutionView.observeHalt]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro h k hk
    exact h k (Finset.mem_univ k) hk
  · intro h k _ hk
    exact h k hk

/-- Equality to an erased program transports its exact step function, not just
its denoted result. Heterogeneous equality accounts only for the bundled types. -/
theorem step_of_erase_eq (m : Machine) (r : RawMachine) (h : erase m = r) :
    HEq r.view.step m.computer.step := by
  cases h
  rfl

theorem start_of_erase_eq (m : Machine) (r : RawMachine) (h : erase m = r) :
    HEq r.view.start (initList m.computer) := by
  cases h
  apply heq_of_eq
  funext word
  exact view_erase_start m word

theorem output_of_erase_eq (m : Machine) (r : RawMachine) (h : erase m = r) :
    HEq r.view.output m.output := by
  cases h
  rfl

theorem observer_of_erase_eq (m : Machine) (r : RawMachine) (h : erase m = r) :
    HEq r.view.observeHalt
      (fun c : m.Config => (c.stk m.output, decide (∀ k, k ≠ m.output → c.stk k = []))) := by
  cases h
  apply heq_of_eq
  funext c
  exact view_erase_observer m c

def leftLayout (a b : RawMachine) : StackEmbedding a.K (a.K ⊕ (b.K ⊕ Unit)) where
  key := Sum.inl
  lift tapes := Sum.elim tapes (fun _ => [])
  lookup _ _ := rfl
  update tapes k word := by
    funext key
    cases key with
    | inl i => by_cases h : i = k <;> simp [Function.update, h, -Sum.elim_update_left,
        -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
    | inr j => simp [Function.update, -Sum.elim_update_left, -Sum.update_elim_inl,
        -Sum.elim_update_right, -Sum.update_elim_inr]

def rightLayout (a b : RawMachine) : StackEmbedding b.K (a.K ⊕ (b.K ⊕ Unit)) where
  key k := .inr (.inl k)
  lift tapes := Sum.elim (fun _ => []) (Sum.elim tapes (fun _ => []))
  lookup _ _ := rfl
  update tapes k word := by
    funext key
    cases key with
    | inl i => simp [Function.update, -Sum.elim_update_left, -Sum.update_elim_inl,
        -Sum.elim_update_right, -Sum.update_elim_inr]
    | inr j =>
      cases j with
      | inl i => by_cases h : i = k <;> simp [Function.update, h, -Sum.elim_update_left,
          -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
      | inr u => simp [Function.update, -Sum.elim_update_left, -Sum.update_elim_inl,
          -Sum.elim_update_right, -Sum.update_elim_inr]

def leftStates (a b : RawMachine) : StateEmbedding a.State (Option Bool × (a.State × b.State)) where
  put state := (none, state, b.initial)
  get state := state.2.1
  get_put _ := rfl

def rightStates (a b : RawMachine) : StateEmbedding b.State (Option Bool × (a.State × b.State)) where
  put state := (none, a.initial, state)
  get state := state.2.2
  get_put _ := rfl

/-- Same finite syntax as `Machine.compose`, omitting enumeration-only fields. -/
def compose (a b : RawMachine) : RawMachine where
  K := a.K ⊕ (b.K ⊕ Unit)
  input := .inl a.input
  output := .inr (.inl b.output)
  Label := a.Label ⊕ (b.Label ⊕ Bool)
  main := .inl a.main
  State := Option Bool × (a.State × b.State)
  initial := (none, a.initial, b.initial)
  program
    | .inl label => embedStmt (leftLayout a b) (leftStates a b) Sum.inl
        (some (.inr (.inr false))) (a.program label)
    | .inr (.inl label) => embedStmt (rightLayout a b) (rightStates a b) (fun l => .inr (.inl l))
        none (b.program label)
    | .inr (.inr false) => copyMoveStmt (.inl a.output) (.inr (.inr ()))
        (.inr (.inr false)) (.inr (.inr true))
    | .inr (.inr true) => copyMoveStmt (.inr (.inr ())) (.inr (.inl b.input))
        (.inr (.inr true)) (.inr (.inl b.main))

@[simp] theorem erase_compose (a b : Machine) : erase (a.compose b) = (erase a).compose (erase b) := by
  unfold erase Machine.compose compose
  congr 1
  funext label
  cases label with
  | inl l => rfl
  | inr l =>
    cases l with
    | inl l => rfl
    | inr b => cases b <;> rfl

def frameLayout (m : RawMachine) : StackEmbedding m.K (m.K ⊕ Bool) where
  key := Sum.inl
  lift tapes := Sum.elim tapes (fun b => if b then [] else [])
  lookup _ _ := rfl
  update tapes k word := by
    funext key
    cases key with
    | inl j => by_cases h : j = k <;> simp [Function.update, h]
    | inr b => simp [Function.update]

def frameStates (m : RawMachine) : StateEmbedding m.State (Option Bool × m.State) where
  put state := (none, state)
  get := Prod.snd
  get_put _ := rfl

/-- Same returning parse/call/serialize syntax as `LeftMap.machine`. -/
def leftMap (m : RawMachine) : RawMachine where
  K := m.K ⊕ Bool
  input := .inr false
  output := .inr false
  Label := m.Label ⊕ Fin 6
  main := .inr 0
  State := Option Bool × m.State
  initial := (none, m.initial)
  program
    | .inl label => embedStmt (frameLayout m) (frameStates m) Sum.inl (some (.inr (2 : Fin 6))) (m.program label)
    | .inr l => if l = 0 then GraphPreprocessing.Frame.scanStmt (.inr false) (.inr true) (.inr 0) (.inr 1) (.inr 5)
      else if l = 1 then copyMoveStmt (.inr true) (.inl m.input) (.inr 1) (.inl m.main)
      else if l = 2 then copyMoveStmt (.inl m.output) (.inr true) (.inr 2) (.inr 3)
      else if l = 3 then FrameEmit.delimiterStmt (.inr false) (.inr 4)
      else if l = 4 then FrameEmit.emitStmt (.inr true) (.inr false) (.inr 4) (.inr 5)
      else .halt

@[simp] theorem erase_leftMap (m : Machine) : erase (LeftMap.machine m) = (erase m).leftMap := by
  unfold erase LeftMap.machine leftMap
  congr 1
  funext label
  cases label with
  | inl l => rfl
  | inr l => rfl

abbrev rightMap (m : RawMachine) : RawMachine :=
  ((erase Wiring.swapMachine).compose m.leftMap).compose (erase Wiring.swapMachine)
abbrev pair (a b : RawMachine) : RawMachine :=
  ((erase Wiring.diagonalMachine).compose a.leftMap).compose b.rightMap

@[simp] theorem erase_rightMap (m : Machine) : erase (rightMapMachine m) = (erase m).rightMap := by
  simp only [rightMapMachine, rightMap, erase_compose, erase_leftMap]
@[simp] theorem erase_pair (a b : Machine) : erase (pairMachine a b) = (erase a).pair (erase b) := by
  simp only [pairMachine, pair, erase_compose, erase_leftMap]

end RawMachine
end Holant.Complexity.FixedFieldMachines
