import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Execution


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Iteration
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.ProductMachine
variable {A : Type} (e : Encoding A Bool) {f : A → A}

abbrev State := ℕ × (A × A)
def encoding := pairEncoding encodingNatBool (pairEncoding e e)
def bodyValue (f : A → A) (s : State (A := A)) : Bool × State (A := A) :=
  (decide (s.1≠0),s.1-1,f s.2.1,s.2.1)

noncomputable def body (w : Executes e e f) :
    Executes (encoding e) (pairEncoding encodingBoolBool (encoding e)) (bodyValue f) := by
  let n := Executes.ofComputes (Wiring.firstComputes encodingNatBool (pairEncoding e e))
  let a := Executes.ofComputes ((Wiring.secondComputes encodingNatBool (pairEncoding e e)).andThen
    (Wiring.firstComputes e e))
  let flag := Executes.ofComputes ((pairComputes
    (Wiring.firstComputes encodingNatBool (pairEncoding e e))
    (constantComputes (encoding e) encodingNatBool 0)).andThen Endpoints.equalComputes |>.andThen
      Rewrite.negComputes)
  let next := Executes.pair (n.comp (Executes.ofComputes Rewrite.predComputes))
    (Executes.pair (a.comp w) a)
  exact (Executes.congr (Executes.pair flag next) (fun s => by simp [bodyValue])).comp
    (Executes.ofComputes (identityComputes (pairEncoding encodingBoolBool (encoding e))))

theorem disjoint (w : Executes e e f) : (body e w).machine.output ≠ (body e w).machine.input := by
  intro h; cases h
noncomputable def machine (w : Executes e e f) := ReturningLoop.machine (body e w).machine

noncomputable def bound (e : Encoding A Bool) (w : Executes e e f) : ℕ → A → A → ℕ
  | 0,a,old => (body e w).cost (0,a,old)+2*((encoding e).encode (0,f a,a)).length+4
  | n+1,a,old => (body e w).cost (n+1,a,old)+
      2*((encoding e).encode (n,f a,a)).length+3+bound e w n (f a) a

set_option backward.isDefEq.respectTransparency false in
theorem run (w : Executes e e f) (n : ℕ) (a old : A) :
    ∃ ticks, ticks ≤ bound e w n a old ∧
      StackProtocol.RunsExactly (machine e w).computer.step
        (ReturningLoop.ready (body e w).machine (.inl (body e w).machine.main)
          (.inl (body e w).machine.input) ((encoding e).encode (n,a,old)))
        (haltList (machine e w).computer
          ((encoding e).encode (0,(f^[n+1]) a,(f^[n]) a))) ticks := by
  induction n generalizing a old with
  | zero =>
    let o := (body e w).outputs (0,a,old)
    have h := ReturningLoop.stop_run (body e w).machine _ _ o.steps
      (by
        have ho := o.evals_in_steps
        change StackProtocol.RunsExactly (body e w).machine.computer.step
          (initList (body e w).machine.computer ((encoding e).encode (0,a,old)))
          (haltList (body e w).machine.computer
            ((pairEncoding encodingBoolBool (encoding e)).encode (bodyValue f (0,a,old)))) o.steps at ho
        simp only [bodyValue, Nat.zero_sub, Nat.add_sub_cancel, Nat.add_one_ne_zero,
          ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
          pairEncoding, encodingBoolBool, encodeBool] at ho
        exact ho)
    refine ⟨o.steps+2*((encoding e).encode (0,f a,a)).length+4, ?_, ?_⟩
    · have ho := o.steps_le_m; simp only [bound]; omega
    · exact h
  | succ n ih =>
    let o := (body e w).outputs (n+1,a,old)
    have first := ReturningLoop.continue_run (body e w).machine (disjoint e w) _ _ o.steps
      (by
        have ho := o.evals_in_steps
        change StackProtocol.RunsExactly (body e w).machine.computer.step
          (initList (body e w).machine.computer ((encoding e).encode (n+1,a,old)))
          (haltList (body e w).machine.computer
            ((pairEncoding encodingBoolBool (encoding e)).encode (bodyValue f (n+1,a,old)))) o.steps at ho
        simp only [bodyValue, Nat.zero_sub, Nat.add_sub_cancel, Nat.add_one_ne_zero,
          ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true,
          pairEncoding, encodingBoolBool, encodeBool] at ho
        exact ho)
    obtain ⟨t,ht,rest⟩ := ih (f a) a
    refine ⟨t+(o.steps+2*((encoding e).encode (n,f a,a)).length+3), ?_, ?_⟩
    · have ho := o.steps_le_m; simp only [bound]; omega
    · have hrun := first.trans rest
      simp only [Function.iterate_succ_apply] at hrun ⊢
      exact hrun

set_option backward.isDefEq.respectTransparency false in
noncomputable def core (w : Executes e e f) : Executes (encoding e) (encoding e)
    (fun s => (0,(f^[s.1+1]) s.2.1,(f^[s.1]) s.2.1)) where
  machine := machine e w
  cost s := bound e w s.1 s.2.1 s.2.2
  outputs s := by
    let execution := run e w s.1 s.2.1 s.2.2
    exact {
      steps := Classical.choose execution
      evals_in_steps := by
        change StackProtocol.RunsExactly (machine e w).computer.step
          (initList (machine e w).computer ((encoding e).encode s))
          (haltList (machine e w).computer ((encoding e).encode (0,(f^[s.1+1]) s.2.1,(f^[s.1]) s.2.1))) _
        rw [show initList (machine e w).computer ((encoding e).encode s) =
          ReturningLoop.ready (body e w).machine (.inl (body e w).machine.main)
            (.inl (body e w).machine.input) ((encoding e).encode s) from
          ReturningLoop.initial (body e w).machine _]
        exact (Classical.choose_spec execution).2
      steps_le_m := (Classical.choose_spec execution).1 }

/-- Original binary exponent input; a finite Boolean program, no oracle. -/
noncomputable def executes (w : Executes e e f) :
    Executes (pairEncoding encodingNatBool e) e (fun p => (f^[p.1]) p.2) := by
  let n := Wiring.firstComputes encodingNatBool e
  let a := Wiring.secondComputes encodingNatBool e
  let prepare := Executes.ofComputes (pairComputes n (pairComputes a a))
  let extract := Executes.ofComputes ((Wiring.secondComputes encodingNatBool (pairEncoding e e)).andThen
    (Wiring.secondComputes e e))
  exact (prepare.comp (core e w)).comp extract

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Iteration
