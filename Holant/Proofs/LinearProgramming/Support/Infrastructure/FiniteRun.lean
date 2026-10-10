import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Complexity.RationalArithmetic.Operations
import Holant.Proofs.LinearProgramming.Support.Infrastructure.BitmapIterateCall
import Holant.Proofs.LinearProgramming.Support.Infrastructure.BitmapIterateFinish

/-!
A weaker, explicit length-bound interface is used here for exact sparse powers.
It still contains an actual finite Boolean-stack Machine, clean timed runs and
a proved monotone total time function. This is NOT BinaryCompose.Computes/InFP.
All constructors below preserve physical programs; no host callback is added
to the TM2 instruction set.
-/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines

structure FiniteComputes {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool) (f : A → B) where
  machine : Machine
  time : ℕ → ℕ
  time_mono : Monotone time
  outputs : ∀ a, TM2OutputsInTime machine.computer (ea.encode a) (some (eb.encode (f a)))
    (time (ea.encode a).length)

namespace FiniteComputes
noncomputable section
variable {A B C D : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
  {ec : Encoding C Bool} {ed : Encoding D Bool} {f : A → B} {g : B → C}

def ofPoly (w : Computes ea eb f) : FiniteComputes ea eb f :=
  ⟨w.machine, w.time.eval, fun _ _ h => natPolynomial_eval_mono w.time h, w.outputs⟩

/-- Standard mathlib machine-computability interface, with the identical
program and explicit non-polynomial time function. -/
def toTM2ComputableInTime (w : FiniteComputes ea eb f) :
    Turing.TM2ComputableInTime ea.encode eb.encode f where
  tm := w.machine.computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := w.time
  outputsFun a := by
    change TM2OutputsInTime w.machine.computer (List.map id (ea.encode a))
      (some (List.map id (eb.encode (f a)))) (w.time (ea.encode a).length)
    simpa only [List.map_id] using w.outputs a

def width (w : FiniteComputes ea eb f) (n : ℕ) : ℕ := n + w.time n * w.machine.primitiveBudget
theorem width_mono (w : FiniteComputes ea eb f) : Monotone w.width := by
  intro a b hab
  exact Nat.add_le_add hab (Nat.mul_le_mul_right _ (w.time_mono hab))
theorem output_length (w : FiniteComputes ea eb f) (a : A) :
    (eb.encode (f a)).length ≤ w.width (ea.encode a).length :=
  w.machine.output_length_le _ _ _ (w.outputs a)

def congr (w : FiniteComputes ea eb f) {h : A → B} (he : ∀ a, f a = h a) :
    FiniteComputes ea eb h where
  machine := w.machine
  time := w.time
  time_mono := w.time_mono
  outputs a := by simpa only [he a] using w.outputs a

def recode (w : FiniteComputes ea eb f) {h : C → D} (input : C → A)
    (hi : ∀ x, ea.encode (input x) = ec.encode x)
    (ho : ∀ x, eb.encode (f (input x)) = ed.encode (h x)) : FiniteComputes ec ed h where
  machine := w.machine
  time := w.time
  time_mono := w.time_mono
  outputs x := by simpa only [hi, ho] using w.outputs (input x)

def andThen (u : FiniteComputes ea eb f) (v : FiniteComputes eb ec g) :
    FiniteComputes ea ec (g ∘ f) where
  machine := u.machine.compose v.machine
  time n := u.time n + 2 * (u.width n + 1) + v.time (u.width n)
  time_mono := by
    intro a b hab
    exact Nat.add_le_add (Nat.add_le_add (u.time_mono hab)
      (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (u.width_mono hab) 1)))
      (v.time_mono (u.width_mono hab))
  outputs a := by
    have h := Machine.compose_correct u.machine v.machine _ _ _ _ _ (u.outputs a) (v.outputs (f a))
    refine {
      steps := h.steps
      evals_in_steps := h.evals_in_steps
      steps_le_m := h.steps_le_m.trans ?_ }
    have hs := u.output_length a
    exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (Nat.add_le_add_right hs 1)) _) (v.time_mono hs)

def leftMap (ec : Encoding C Bool) (u : FiniteComputes ea eb f) :
    FiniteComputes (pairEncoding ea ec) (pairEncoding eb ec) (fun p => (f p.1,p.2)) where
  machine := LeftMap.machine u.machine
  time n := 2*n + u.time n + 2*u.width n + 6
  time_mono := by
    intro a b hab
    have ht := u.time_mono hab
    have hw := u.width_mono hab
    change 2*a + u.time a + 2*u.width a + 6 ≤ 2*b + u.time b + 2*u.width b + 6
    omega
  outputs p := by
    let h := u.outputs p.1
    refine {
      steps := 2*(ea.encode p.1).length+h.steps+2*(eb.encode (f p.1)).length+6
      evals_in_steps := LeftMap.exact_run u.machine _ _ _ h.steps h.evals_in_steps
      steps_le_m := ?_ }
    have hi : (ea.encode p.1).length ≤ ((pairEncoding ea ec).encode p).length := by
      simp only [pairEncoding_length]; omega
    have ht := h.steps_le_m.trans (u.time_mono hi)
    have hw := (u.output_length p.1).trans (u.width_mono hi)
    omega

def rightMap (ea : Encoding A Bool) {g : B → C} (v : FiniteComputes eb ec g) :
    FiniteComputes (pairEncoding ea eb) (pairEncoding ea ec) (fun p => (p.1,g p.2)) :=
  (((ofPoly (Wiring.swapComputes ea eb)).andThen (v.leftMap ea)).andThen
    (ofPoly (Wiring.swapComputes ec ea))).congr (fun _ => rfl)

def pair {g : A → C} (u : FiniteComputes ea eb f) (v : FiniteComputes ea ec g) :
    FiniteComputes ea (pairEncoding eb ec) (fun a => (f a,g a)) :=
  (((ofPoly (Wiring.diagonalComputes ea)).andThen (u.leftMap ea)).andThen
    (v.rightMap eb)).congr (fun _ => rfl)

/-- Every intermediate configuration has an actual bit bound. No bound on
rational numerators is assumed: only physical pushes can grow the stacks. -/
theorem intermediate_bits (w : FiniteComputes ea eb f) (a : A) {i : ℕ}
    (hi : i ≤ w.time (ea.encode a).length) {c : w.machine.Config}
    (hc : (fun p => p.bind w.machine.computer.step)^[i]
      (some (initList w.machine.computer (ea.encode a))) = some c) :
    stackSize c.stk ≤ w.width (ea.encode a).length := by
  have h := w.machine.run_size_le _ c i hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _)

theorem primitive_bound (w : FiniteComputes ea eb f) (a : A) :
    primitiveCost w.machine (w.outputs a).steps
      (some (initList w.machine.computer (ea.encode a))) ≤
        w.time (ea.encode a).length * w.machine.primitiveBudget :=
  (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ (w.outputs a).steps_le_m)

end
end FiniteComputes
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
