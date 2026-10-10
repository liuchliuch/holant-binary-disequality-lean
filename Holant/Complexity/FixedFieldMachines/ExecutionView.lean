import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! An execution-only projection of a finite machine. It omits the unused
finite-state and finite-label enumerations, which can have exponentially large
Cartesian products even though every executed state is a small nested tuple.
This is an observer interface, not a different machine or simulation model. -/
namespace Holant.Complexity.FixedFieldMachines
open Turing BinaryCompose

structure ExecutionView (K L S : Type) where
  keyEq : DecidableEq K
  step : TM2.Cfg (fun _ : K => Bool) L S → Option (TM2.Cfg (fun _ : K => Bool) L S)
  start : List Bool → TM2.Cfg (fun _ : K => Bool) L S
  output : K
  keys : Finset K

namespace ExecutionView

def ofMachine (m : Machine) : ExecutionView m.K m.Label m.State where
  keyEq := m.decidableK
  step c := m.computer.step c
  start word := initList m.computer word
  output := m.output
  keys := Finset.univ

@[simp] theorem step_ofMachine (m : Machine) : (ofMachine m).step = m.computer.step := rfl
@[simp] theorem start_ofMachine (m : Machine) : (ofMachine m).start = initList m.computer := rfl
@[simp] theorem output_ofMachine (m : Machine) : (ofMachine m).output = m.output := rfl
@[simp] theorem mem_keys (m : Machine) (k : m.K) : k ∈ (ofMachine m).keys := Finset.mem_univ k

/-- Complete final-output/cleanup observation, independent of unused metadata. -/
def observeHalt {K L S : Type} (v : ExecutionView K L S)
    (c : TM2.Cfg (fun _ : K => Bool) L S) : List Bool × Bool :=
  letI := v.keyEq
  (c.stk v.output, decide (∀ k ∈ v.keys, k ≠ v.output → c.stk k = []))

@[simp] theorem observeHalt_ofMachine (m : Machine) (c : m.Config) :
    (ofMachine m).observeHalt c =
      (c.stk m.output, decide (∀ k, k ≠ m.output → c.stk k = [])) := by
  simp [observeHalt, ofMachine]

/-- Observe the literal transition system and all non-output work stacks. -/
def run {K L S : Type} (v : ExecutionView K L S) : ℕ → ℕ →
    TM2.Cfg (fun _ : K => Bool) L S → Option (ℕ × List Bool × Bool)
  | 0, _, _ => none
  | fuel + 1, count, c =>
    letI := v.keyEq
    if c.l.isNone then
      some (count, v.observeHalt c)
    else match v.step c with
      | none => none
      | some d => run v fuel (count + 1) d

def check {K L S : Type} (name : String) (v : ExecutionView K L S)
    (input expected : List Bool) (fuel : ℕ) : IO Unit := do
  match v.run fuel 0 (v.start input) with
  | none => throw (IO.userError s!"{name}: machine did not halt within {fuel} transitions")
  | some (count, word, clean) =>
    if word == expected && clean then
      IO.println s!"{name}: {count} actual transitions; canonical output; all work stacks clear"
    else throw (IO.userError s!"{name}: incorrect output or uncleared work stacks")

/-- Variant retaining the final configuration for independent memory-reset checks. -/
def runConfig {K L S : Type} (v : ExecutionView K L S) : ℕ → ℕ →
    TM2.Cfg (fun _ : K => Bool) L S → Option (ℕ × TM2.Cfg (fun _ : K => Bool) L S)
  | 0, _, _ => none
  | fuel + 1, count, c => if c.l.isNone then some (count, c)
    else match v.step c with
      | none => none
      | some d => runConfig v fuel (count + 1) d

def checkWithState {K L S : Type} (name : String) (v : ExecutionView K L S)
    (stateReset : S → Bool) (input expected : List Bool) (fuel : ℕ) : IO Unit := do
  match v.runConfig fuel 0 (v.start input) with
  | none => throw (IO.userError s!"{name}: machine did not halt within {fuel} transitions")
  | some (count, c) =>
    let (word, clean) := v.observeHalt c
    if word == expected && clean && stateReset c.var then
      IO.println s!"{name}: {count} actual transitions; canonical output; all work stacks and finite memory clear"
    else throw (IO.userError s!"{name}: incorrect output, uncleared work stacks or finite memory")

end ExecutionView
end Holant.Complexity.FixedFieldMachines
