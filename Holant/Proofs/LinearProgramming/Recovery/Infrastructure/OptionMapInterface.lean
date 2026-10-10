import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.OptionMap

set_option autoImplicit false

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure.OptionMap
open Holant.Complexity Holant.Complexity.GraphPreprocessing
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option Elab.async false

/-- A present value executes precisely the source machine, surrounded by
counted tag parsing and two order-preserving physical word transfers. -/
theorem some_exact (input output : List Bool) (n : ℕ)
    (h : (fun p => p.bind m.computer.step)^[n] (some (initList m.computer input)) = some (haltList m.computer output)) :
    Holant.Complexity.StackProtocol.RunsExactly (machine m).computer.step
      (initList (machine m).computer (true::input)) (haltList (machine m).computer (true::output))
      (2*input.length+n+2*output.length+6) := by
  have load := transfer_exact_frame (.inr false : Keys m) (.inl m.input) (.inr true)
    (by intro h; cases h) (by simp) (by intro h; cases h)
    (machine m).computer.step (.inr 1 : Labels m) (.inr 2) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    m.initial (fun _ => []) input []
  rw [← LeftMap.tapes_extract,← LeftMap.tapes_extract] at load
  simp only [List.append_nil] at load
  have core := embed_run (LeftMap.layout m [] []) (LeftMap.states m) Sum.inl (some (.inr (3 : Fin 11)))
    m.program (program m) (fun _ => rfl) (initList m.computer input) (haltList m.computer output) n h
  have hi : embedCfg (LeftMap.layout m [] []) (LeftMap.states m) Sum.inl (some (.inr (3 : Fin 11)))
      (initList m.computer input) = cfg (.inl m.main : Labels m) m.initial (tapes m m.input input [] []) := by
    rw [Machine.init_eq]; rfl
  have ho : embedCfg (LeftMap.layout m [] []) (LeftMap.states m) Sum.inl (some (.inr (3 : Fin 11)))
      (haltList m.computer output) = cfg (.inr 3 : Labels m) m.initial (tapes m m.output output [] []) := by
    rw [Machine.halt_eq]; rfl
  rw [hi,ho] at core
  change Holant.Complexity.StackProtocol.RunsExactly (machine m).computer.step _ _ n at core
  have emit := transfer_exact_frame (.inl m.output : Keys m) (.inr false) (.inr true)
    (by intro h; cases h) (by intro h; cases h) (by simp)
    (machine m).computer.step (.inr 3 : Labels m) (.inr 4) (.inr 5)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    m.initial (fun _ => []) output []
  rw [← LeftMap.tapes_emit,← LeftMap.tapes_emit] at emit
  simp only [List.append_nil] at emit
  have all := ((((runsExactly_one (tag_some m input)).trans load).trans core).trans emit).trans
    (runsExactly_one (halt_some m output))
  rw [← initial]
  convert all using 1
  omega

variable {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool} {f : α → β}

noncomputable def timePolynomial (w : Computes ea eb f) : Polynomial ℕ :=
  4*Polynomial.X + Polynomial.C (1+2*w.machine.primitiveBudget)*w.time+6

/-- A genuine finite-machine closure for the explicit optional-word codec. -/
noncomputable def computes (w : Computes ea eb f) :
    Computes (optionEncoding ea) (optionEncoding eb) (Option.map f) where
  machine := machine w.machine
  time := timePolynomial w
  outputs x := by
    cases x with
    | none =>
      refine {steps := 2, evals_in_steps := none_exact w.machine, steps_le_m := ?_}
      simp only [timePolynomial,optionEncoding,List.length_singleton,Polynomial.eval_add,Polynomial.eval_mul,
        Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat]
      omega
    | some a =>
      let h := w.outputs a
      refine {
        steps := 2*(ea.encode a).length+h.steps+2*(eb.encode (f a)).length+6
        evals_in_steps := some_exact w.machine _ _ h.steps h.evals_in_steps
        steps_le_m := ?_ }
      have hi : (ea.encode a).length ≤ ((optionEncoding ea).encode (some a)).length := by
        simp [optionEncoding]
      have ht := natPolynomial_eval_mono w.time hi
      have hs := h.steps_le_m
      have ho := w.machine.output_length_le _ _ _ h
      simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
        Polynomial.eval_X,Polynomial.eval_ofNat]
      nlinarith

@[simp] theorem computes_machine (w : Computes ea eb f) : (computes w).machine = machine w.machine := rfl

theorem inFP (w : Computes ea eb f) : InFP (optionEncoding ea) (optionEncoding eb) (Option.map f) :=
  (computes w).inFP

end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure.OptionMap
