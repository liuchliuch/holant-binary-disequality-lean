import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionExecution

/-! Literal outputs of one deterministic finite machine are unique. This
allows two independently derived canonical graph expansions to be identified
as syntax, with no appeal to equal arithmetic denotations. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
open Turing Computability StackProtocol BinaryCompose

 theorem reaches_of_iterate {S : Type*} (step : S → Option S) (n : ℕ) (a b : S)
    (h : (fun c => c.bind step)^[n] (some a) = some b) : StateTransition.Reaches step a b := by
  induction n generalizing b with
  | zero =>
    have he : a = b := Option.some.inj h
    subst b
    exact .refl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hs : (fun c => c.bind step)^[n] (some a) with
    | none => simp [hs] at h
    | some c =>
      exact (ih c hs).tail (by simpa only [hs,Option.bind_some,Option.mem_def] using h)

 theorem machine_output_unique (m : Machine) (input left right : List Bool) (n k : ℕ)
    (hl : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer input)) = some (haltList m.computer left))
    (hr : (fun c => c.bind m.computer.step)^[k] (some (initList m.computer input)) = some (haltList m.computer right)) :
    left = right := by
  have hleft : haltList m.computer left ∈ StateTransition.eval m.computer.step (initList m.computer input) :=
    StateTransition.mem_eval.mpr ⟨reaches_of_iterate _ n _ _ hl,rfl⟩
  have hright : haltList m.computer right ∈ StateTransition.eval m.computer.step (initList m.computer input) :=
    StateTransition.mem_eval.mpr ⟨reaches_of_iterate _ k _ _ hr,rfl⟩
  have hc := Part.mem_unique hleft hright
  rw [m.halt_eq,m.halt_eq] at hc
  have h := congrArg (fun c : m.Config => c.stk m.output) hc
  simpa only [wordTape_at] using h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
