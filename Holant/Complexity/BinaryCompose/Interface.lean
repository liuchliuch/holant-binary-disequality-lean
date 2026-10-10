import Holant.Complexity.Encoding
import Holant.Complexity.OracleQueryBounds

/-!
# Uniform Boolean-stack polynomial-time machines

Unlike an arbitrary `FinTM2`, this interface fixes every internal alphabet to
`Bool`. It records an actual finite program and standard clean `initList` /
`haltList` correctness. Forgetting this extra uniformity gives ordinary `PolyTime`.
-/

namespace Holant.Complexity.BinaryCompose
open Turing Computability

/-- An actual finite machine with a uniformly Boolean stack alphabet. The input
and output stacks may be identical. -/
structure Machine where
  K : Type
  [decidableK : DecidableEq K]
  [finiteK : Fintype K]
  input : K
  output : K
  Label : Type
  [finiteLabel : Fintype Label]
  main : Label
  State : Type
  [finiteState : Fintype State]
  initial : State
  program : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] Machine.decidableK Machine.finiteK Machine.finiteLabel Machine.finiteState

/-- The interface's machine is an ordinary bundled finite TM2. -/
abbrev Machine.computer (m : Machine) : FinTM2 where
  K := m.K
  k₀ := m.input
  k₁ := m.output
  Γ _ := Bool
  Λ := m.Label
  main := m.main
  σ := m.State
  initialState := m.initial
  m := m.program

abbrev Machine.Config (m : Machine) := TM2.Cfg (fun _ : m.K => Bool) m.Label m.State

/-- A single populated tape, used only in specifications. -/
def wordTape {K : Type} [DecidableEq K] (key : K) (word : List Bool) : K → List Bool :=
  Function.update (fun _ => []) key word

@[simp] theorem wordTape_at {K : Type} [DecidableEq K] (key : K) (word : List Bool) :
    wordTape key word key = word := by simp [wordTape]

@[simp] theorem wordTape_other {K : Type} [DecidableEq K] (key k : K)
    (word : List Bool) (h : k ≠ key) : wordTape key word k = [] := by simp [wordTape, h]

/-- The readable Boolean tape presentation equals mathlib's dependent convention. -/
theorem Machine.init_eq (m : Machine) (input : List Bool) :
    initList m.computer input = ⟨some m.main, m.initial, wordTape m.input input⟩ := by
  dsimp [initList, Machine.computer]
  congr 1
  funext k
  by_cases h : k = m.input <;> simp [h, wordTape, Function.update]

theorem Machine.halt_eq (m : Machine) (output : List Bool) :
    haltList m.computer output = ⟨none, m.initial, wordTape m.output output⟩ := by
  dsimp [haltList, Machine.computer]
  congr 1
  funext k
  by_cases h : k = m.output <;> simp [h, wordTape, Function.update]

/-- A clean operational witness, with no oracle or host-language word operation. -/
structure Computes {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool) (f : α → β) where
  machine : Machine
  time : Polynomial ℕ
  outputs : ∀ a, TM2OutputsInTime machine.computer (ea.encode a) (some (eb.encode (f a)))
    (time.eval (ea.encode a).length)

/-- Uniform Boolean witnesses immediately supply the project's ordinary notion. -/
def Computes.toPolyTime {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {f : α → β} (w : Computes ea eb f) : PolyTime ea eb f where
  tm := w.machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := w.time
  outputsFun a := by
    change TM2OutputsInTime w.machine.computer (List.map id (ea.encode a))
      (some (List.map id (eb.encode (f a)))) (w.time.eval (ea.encode a).length)
    rw [List.map_id, List.map_id]
    exact w.outputs a
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

theorem Computes.inFP {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {f : α → β} (w : Computes ea eb f) : InFP ea eb f := ⟨w.toPolyTime⟩

end Holant.Complexity.BinaryCompose
