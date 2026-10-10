import Holant.Complexity.BinaryCompose.Composition
import Holant.Complexity.OracleSpace

/-! Output-size bounds derived from actual ordinary Boolean-machine transitions.
This eliminates any separate size assumption for the default composition API. -/

namespace Holant.Complexity.BinaryCompose
open Turing Computability
open scoped BigOperators

namespace Machine

/-- A fixed elementary-instruction bound for a finite program. -/
def primitiveBudget (m : Machine) : ℕ := ∑ label, TM2Cost.budget (m.program label)

theorem program_budget_le (m : Machine) (label : m.Label) :
    TM2Cost.budget (m.program label) ≤ m.primitiveBudget := by
  unfold primitiveBudget
  exact Finset.single_le_sum (f := fun l : m.Label => TM2Cost.budget (m.program l))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)

/-- Each executed transition grows stored data only through explicit pushes. -/
theorem step_size_le (m : Machine) (c d : m.Config) (h : m.computer.step c = some d) :
    stackSize d.stk ≤ stackSize c.stk + m.primitiveBudget := by
  rcases c with ⟨label, v, tapes⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at h
  | some label =>
    have hd : TM2.stepAux (m.program label) v tapes = d := Option.some.inj h
    subst d
    exact le_trans (TM2Cost.stepAux_size_le _ _ _) (Nat.add_le_add_left (m.program_budget_le label) _)

/-- Real run length bounds total tape storage. -/
theorem run_size_le (m : Machine) (c d : m.Config) (n : ℕ)
    (h : (fun p => p.bind m.computer.step)^[n] (some c) = some d) :
    stackSize d.stk ≤ stackSize c.stk + n * m.primitiveBudget := by
  change (fun p => p.bind (TM2.step m.program))^[n] (some c) = some d at h
  induction n generalizing d with
  | zero =>
    have hd : c = d := Option.some.inj h
    subst d
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (TM2.step m.program))^[n] (some c) with
    | none => simp [hp] at h
    | some previous =>
      have hs : TM2.step m.program previous = some d := by
        simpa only [hp, Option.bind_some] using h
      have hprev := ih previous hp
      have hstep := m.step_size_le previous d hs
      rw [Nat.add_mul, Nat.one_mul]
      omega

@[simp] theorem stackSize_wordTape {K : Type} [Fintype K] [DecidableEq K]
    (key : K) (word : List Bool) : stackSize (wordTape key word) = word.length := by
  simp [wordTape, stackSize, Function.update, apply_ite]

@[simp] theorem size_init (m : Machine) (word : List Bool) :
    stackSize (initList m.computer word).stk = word.length := by rw [m.init_eq]; simp

@[simp] theorem size_halt (m : Machine) (word : List Bool) :
    stackSize (haltList m.computer word).stk = word.length := by rw [m.halt_eq]; simp

/-- Clean outputs cannot silently introduce an unbounded word. -/
theorem output_length_le (m : Machine) (input output : List Bool) (time : ℕ)
    (h : TM2OutputsInTime m.computer input (some output) time) :
    output.length ≤ input.length + time * m.primitiveBudget := by
  have hs := m.run_size_le (initList m.computer input) (haltList m.computer output)
    h.steps h.evals_in_steps
  rw [size_init, size_halt] at hs
  exact le_trans hs (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Machine

/-- Source-output size follows from the source program and timed correctness. -/
noncomputable def Computes.outputBound {α β : Type} {ea : Encoding α Bool}
    {eb : Encoding β Bool} {f : α → β} (w : Computes ea eb f) :
    PolynomialOutputBound ea eb f where
  bound := Polynomial.X + w.time * Polynomial.C w.machine.primitiveBudget
  length_le x := by
    simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
      using w.machine.output_length_le (ea.encode x) (eb.encode (f x))
        (w.time.eval (ea.encode x).length) (w.outputs x)

/-- Unconditional sequential closure for the Boolean-machine interface. Its
intermediate-length bound is proved from real transitions, not supplied as an
annotation or a unit-cost word primitive. -/
noncomputable def Computes.andThen {α β γ : Type} {ea : Encoding α Bool}
    {eb : Encoding β Bool} {ec : Encoding γ Bool} {f : α → β} {g : β → γ}
    (a : Computes ea eb f) (b : Computes eb ec g) : Computes ea ec (g ∘ f) :=
  a.comp b a.outputBound

/-- Ordinary finite-machine polynomial time after operational composition. -/
noncomputable def polyTimeAndThen {α β γ : Type} {ea : Encoding α Bool}
    {eb : Encoding β Bool} {ec : Encoding γ Bool} {f : α → β} {g : β → γ}
    (a : Computes ea eb f) (b : Computes eb ec g) : PolyTime ea ec (g ∘ f) :=
  (a.andThen b).toPolyTime

end Holant.Complexity.BinaryCompose
