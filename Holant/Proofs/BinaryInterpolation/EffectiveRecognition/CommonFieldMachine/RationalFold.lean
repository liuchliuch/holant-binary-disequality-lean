import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.GrowingLoop
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Coordinates
import Holant.Complexity.BinaryCompose.Composition


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.RationalFold
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.CertificateMachine

abbrev State := List ℚ × (ℕ × ℚ)
abbrev encoding := pairEncoding coordinatesEncoding
  (pairEncoding UnaryBinary.unaryEncoding rationalEncoding)
def step (s : State) : State := (s.1,s.2.1+1,s.2.2+s.1.getD s.2.1 0)
def initial (xs : List ℚ) : State := (xs,0,0)

noncomputable def stepComputes : Computes encoding encoding step := by
  let xs := Wiring.firstComputes coordinatesEncoding
    (pairEncoding UnaryBinary.unaryEncoding rationalEncoding)
  let tail := Wiring.secondComputes coordinatesEncoding
    (pairEncoding UnaryBinary.unaryEncoding rationalEncoding)
  let index := tail.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding rationalEncoding)
  let acc := tail.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding rationalEncoding)
  exact pairComputes xs (pairComputes (index.andThen WireLists.succComputes)
    (Scalars.add acc (AccessPrograms.get rationalEncoding 0 xs index)))

theorem take_sum_succ (xs : List ℚ) (n : ℕ) :
    (xs.take (n+1)).sum = (xs.take n).sum + xs.getD n 0 := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n => simpa [List.take, add_assoc] using congrArg (x + ·) (ih n)

theorem iterate_initial (xs : List ℚ) (k : ℕ) :
    (step^[k]) (initial xs) = (xs,k,(xs.take k).sum) := by
  induction k with
  | zero => simp [initial]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, take_sum_succ]

theorem initial_length (xs : List ℚ) : xs.length ≤ (encoding.encode (initial xs)).length := by
  have h := framedListEncoding_length_lower rationalEncoding xs
  change 2*xs.length+1 ≤ (coordinatesEncoding.encode xs).length at h
  simp only [encoding, initial, pairEncoding_length]
  omega

theorem value_acc (xs : List ℚ) :
    (GrowingLoop.value encoding step (initial xs)).2.2 = xs.sum := by
  rw [GrowingLoop.value, iterate_initial, List.take_of_length_le (initial_length xs)]

noncomputable def prepare : Computes coordinatesEncoding (GrowingLoop.inputEncoding encoding) initial := by
  let state := pairComputes (identityComputes coordinatesEncoding)
    (pairComputes (constantComputes coordinatesEncoding UnaryBinary.unaryEncoding 0)
      (constantComputes coordinatesEncoding rationalEncoding 0))
  exact recode ((pairComputes state (constantComputes coordinatesEncoding Frame.wordEncoding [])))
    id (fun _ => rfl) (fun xs => by simp [pairEncoding, GrowingLoop.inputEncoding,
      Frame.wordEncoding, initial])

noncomputable def extract : Computes encoding rationalEncoding (fun s => s.2.2) :=
  (Wiring.secondComputes coordinatesEncoding (pairEncoding UnaryBinary.unaryEncoding rationalEncoding)).andThen
    (Wiring.secondComputes UnaryBinary.unaryEncoding rationalEncoding)

noncomputable def machine : Machine :=
  (prepare.machine.compose (GrowingLoop.machine stepComputes)).compose extract.machine

/-- The displayed recursive bound includes both physical composition transfers. -/
noncomputable def bound (xs : List ℚ) : ℕ :=
  let s := initial xs
  let t := GrowingLoop.value encoding step s
  prepare.time.eval (coordinatesEncoding.encode xs).length +
    2*(((GrowingLoop.inputEncoding encoding).encode s).length+1) +
    GrowingLoop.bound stepComputes s + 2*((encoding.encode t).length+1) +
    extract.time.eval (encoding.encode t).length

noncomputable def outputs (xs : List ℚ) :
    TM2OutputsInTime machine.computer (coordinatesEncoding.encode xs)
      (some (rationalEncoding.encode xs.sum)) (bound xs) := by
  let s := initial xs
  let t := GrowingLoop.value encoding step s
  let execution := GrowingLoop.whole_run stepComputes s
  let ticks := Classical.choose execution
  have ht := (Classical.choose_spec execution).1
  have run := (Classical.choose_spec execution).2
  have middle : TM2OutputsInTime (GrowingLoop.machine stepComputes).computer
      ((GrowingLoop.inputEncoding encoding).encode s) (some (encoding.encode t))
      (GrowingLoop.bound stepComputes s) := {
        steps := ticks
        evals_in_steps := run
        steps_le_m := ht }
  have first := Machine.compose_correct prepare.machine (GrowingLoop.machine stepComputes)
    _ _ _ _ _ (prepare.outputs xs) middle
  have last := Machine.compose_correct (prepare.machine.compose (GrowingLoop.machine stepComputes))
    extract.machine _ _ _ _ _ first (extract.outputs t)
  simpa only [machine, bound, t, s, value_acc, Nat.add_assoc] using last

theorem primitive_bound (xs : List ℚ) :
    primitiveCost machine (outputs xs).steps
      (some (initList machine.computer (coordinatesEncoding.encode xs))) ≤
        bound xs * machine.primitiveBudget :=
  (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ (outputs xs).steps_le_m)

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.RationalFold
