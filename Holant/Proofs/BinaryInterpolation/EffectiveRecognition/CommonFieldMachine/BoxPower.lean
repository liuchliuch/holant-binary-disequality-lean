import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.ReturningLoop


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.BoxPower
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open StackProtocol
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.ProductMachine

abbrev State := ℕ × (RationalBox × RationalBox)
abbrev encoding := pairEncoding encodingNatBool (pairEncoding boxEncoding boxEncoding)
def next (s : State) : State :=
  (s.1-1,s.2.1,if s.1=0 then s.2.2 else s.2.2.mul s.2.1)
def bodyValue (s : State) : Bool × State := (decide (s.1≠0),next s)

noncomputable def bodyCore : Computes encoding (pairEncoding encodingBoolBool encoding) bodyValue := by
  let n := Wiring.firstComputes encodingNatBool (pairEncoding boxEncoding boxEncoding)
  let boxes := Wiring.secondComputes encodingNatBool (pairEncoding boxEncoding boxEncoding)
  let base := boxes.andThen (Wiring.firstComputes boxEncoding boxEncoding)
  let acc := boxes.andThen (Wiring.secondComputes boxEncoding boxEncoding)
  let isZero := (pairComputes n (constantComputes encoding encodingNatBool 0)).andThen
    Endpoints.equalComputes
  let flag := isZero.andThen Rewrite.negComputes
  let acc' := ifComputes isZero acc (BoxPrimitives.mul acc base)
  exact congrComputes (pairComputes flag
    (pairComputes (n.andThen Rewrite.predComputes) (pairComputes base acc')))
    (fun s => by simp [bodyValue, next])

/-- The identity suffix supplies disjoint source/destination keys even if an
underlying scalar routine aliases its own input and output. -/
noncomputable def body : Computes encoding (pairEncoding encodingBoolBool encoding) bodyValue :=
  bodyCore.andThen (identityComputes (pairEncoding encodingBoolBool encoding))

theorem body_disjoint : body.machine.output ≠ body.machine.input := by
  intro h
  cases h

noncomputable def machine := ReturningLoop.machine body.machine

def accumulated (b : RationalBox) (k : ℕ) (a : RationalBox) : RationalBox :=
  ((fun x => x.mul b)^[k]) a

@[simp] theorem accumulated_zero (b a : RationalBox) : accumulated b 0 a = a := rfl
theorem accumulated_succ (b a : RationalBox) (k : ℕ) :
    accumulated b (k+1) a = accumulated b k (a.mul b) :=
  Function.iterate_succ_apply _ _ _
theorem accumulated_point (b : RationalBox) (k : ℕ) :
    accumulated b k (RationalBox.point 1) = RationalBox.power b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [accumulated, Function.iterate_succ_apply', RationalBox.power] at *
    rw [ih]

noncomputable def bound : ℕ → RationalBox → RationalBox → ℕ
  | 0,b,a => body.time.eval (encoding.encode (0,b,a)).length +
      2*(encoding.encode (0,b,a)).length+4
  | k+1,b,a => body.time.eval (encoding.encode (k+1,b,a)).length +
      2*(encoding.encode (k,b,a.mul b)).length+3+bound k b (a.mul b)

set_option backward.isDefEq.respectTransparency false in
/-- Termination is proved by the binary countdown's numerical value, with an
actual return run at each step; no successful whole-machine run is an input. -/
theorem run (k : ℕ) (b a : RationalBox) :
    ∃ ticks, ticks ≤ bound k b a ∧
      RunsExactly machine.computer.step
        (ReturningLoop.ready body.machine (.inl body.machine.main) (.inl body.machine.input)
          (encoding.encode (k,b,a)))
        (haltList machine.computer (encoding.encode (0,b,accumulated b k a))) ticks := by
  induction k generalizing a with
  | zero =>
    let o := body.outputs (0,b,a)
    have r := ReturningLoop.stop_run body.machine (encoding.encode (0,b,a))
      (encoding.encode (0,b,a)) o.steps
      (by
        have ho := o.evals_in_steps
        change RunsExactly body.machine.computer.step
          (initList body.machine.computer (encoding.encode (0,b,a)))
          (haltList body.machine.computer ((pairEncoding encodingBoolBool encoding).encode
            (bodyValue (0,b,a)))) o.steps at ho
        simp only [bodyValue, next, Nat.zero_sub, ne_eq, not_true_eq_false, decide_false,
          ite_true, pairEncoding, encodingBoolBool, encodeBool] at ho
        exact ho)
    exact ⟨o.steps+2*(encoding.encode (0,b,a)).length+4,
      by have h := o.steps_le_m; simp only [bound]; omega,r⟩
  | succ k ih =>
    let o := body.outputs (k+1,b,a)
    have first := ReturningLoop.continue_run body.machine body_disjoint
      (encoding.encode (k+1,b,a)) (encoding.encode (k,b,a.mul b)) o.steps
      (by
        have ho := o.evals_in_steps
        change RunsExactly body.machine.computer.step
          (initList body.machine.computer (encoding.encode (k+1,b,a)))
          (haltList body.machine.computer ((pairEncoding encodingBoolBool encoding).encode
            (bodyValue (k+1,b,a)))) o.steps at ho
        simp only [bodyValue, next, Nat.add_sub_cancel, Nat.add_one_ne_zero,
          ne_eq, not_false_eq_true, decide_true, ite_false,
          pairEncoding, encodingBoolBool, encodeBool] at ho
        exact ho)
    obtain ⟨t,ht,rest⟩ := ih (a.mul b)
    refine ⟨t+(o.steps+2*(encoding.encode (k,b,a.mul b)).length+3), ?_, ?_⟩
    · have ho := o.steps_le_m
      simp only [bound]
      omega
    · rw [accumulated_succ]
      exact first.trans rest

set_option backward.isDefEq.respectTransparency false in
noncomputable def outputs (s : State) :
    TM2OutputsInTime machine.computer (encoding.encode s)
      (some (encoding.encode (0,s.2.1,accumulated s.2.1 s.1 s.2.2)))
      (bound s.1 s.2.1 s.2.2) := by
  let execution := run s.1 s.2.1 s.2.2
  exact {
    steps := Classical.choose execution
    evals_in_steps := by
      change RunsExactly machine.computer.step
        (initList machine.computer (encoding.encode s))
        (haltList machine.computer (encoding.encode (0,s.2.1,accumulated s.2.1 s.1 s.2.2))) _
      rw [show initList machine.computer (encoding.encode s) =
        ReturningLoop.ready body.machine (.inl body.machine.main) (.inl body.machine.input)
          (encoding.encode s) from ReturningLoop.initial body.machine _]
      exact (Classical.choose_spec execution).2
    steps_le_m := (Classical.choose_spec execution).1 }

abbrev inputEncoding := pairEncoding encodingNatBool boxEncoding
def start (p : ℕ × RationalBox) : State := (p.1,p.2,RationalBox.point 1)
noncomputable def prepare : Computes inputEncoding encoding start :=
  pairComputes (Wiring.firstComputes encodingNatBool boxEncoding)
    (pairComputes (Wiring.secondComputes encodingNatBool boxEncoding)
      (constantComputes inputEncoding boxEncoding (RationalBox.point 1)))
noncomputable def extract : Computes encoding boxEncoding (fun s => s.2.2) :=
  (Wiring.secondComputes encodingNatBool (pairEncoding boxEncoding boxEncoding)).andThen
    (Wiring.secondComputes boxEncoding boxEncoding)
noncomputable def powerMachine : Machine := (prepare.machine.compose machine).compose extract.machine

noncomputable def powerBound (p : ℕ × RationalBox) : ℕ :=
  let s := start p
  let out : State := (0,p.2,RationalBox.power p.2 p.1)
  prepare.time.eval (inputEncoding.encode p).length + 2*((encoding.encode s).length+1) +
    bound p.1 p.2 (RationalBox.point 1) + 2*((encoding.encode out).length+1) +
    extract.time.eval (encoding.encode out).length

noncomputable def power_outputs (p : ℕ × RationalBox) :
    TM2OutputsInTime powerMachine.computer (inputEncoding.encode p)
      (some (boxEncoding.encode (RationalBox.power p.2 p.1))) (powerBound p) := by
  have first := Machine.compose_correct prepare.machine machine _ _ _ _ _
    (prepare.outputs p) (outputs (start p))
  have last := Machine.compose_correct (prepare.machine.compose machine) extract.machine _ _ _ _ _
    first (extract.outputs (0,p.2,accumulated p.2 p.1 (RationalBox.point 1)))
  simpa only [powerMachine, powerBound, start, accumulated_point, Nat.add_assoc] using last

theorem primitive_bound (p : ℕ × RationalBox) :
    primitiveCost powerMachine (power_outputs p).steps
      (some (initList powerMachine.computer (inputEncoding.encode p))) ≤
        powerBound p * powerMachine.primitiveBudget :=
  (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ (power_outputs p).steps_le_m)

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.BoxPower
