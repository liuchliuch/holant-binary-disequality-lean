import Holant.Proofs.LinearProgramming.Support.Infrastructure.ReverseFold

/-!
Retiming certificates refer to the EXACT steps of the old timed run. Converting
one to Computes retains its machine, output witness and number of transitions.
Composition charges the actual transfer words; output/temporary sizes follow
from physical pushes, not an assumed arithmetic unit-cost model.
-/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure

structure Timing {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool} {f : A → B}
    (w : FiniteComputes ea eb f) where
  bound : Polynomial ℕ
  steps_le : ∀ a,(w.outputs a).steps≤bound.eval (ea.encode a).length

namespace Timing
noncomputable section
variable {A B C D : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
  {ec : Encoding C Bool} {ed : Encoding D Bool} {f : A → B} {g : B → C}
  {u : FiniteComputes ea eb f} {v : FiniteComputes eb ec g}

def computes (t : Timing u) : Computes ea eb f where
  machine := u.machine
  time := t.bound
  outputs a := {
    steps := (u.outputs a).steps
    evals_in_steps := (u.outputs a).evals_in_steps
    steps_le_m := t.steps_le a }

theorem computes_steps (t : Timing u) (a : A) :
    (t.computes.outputs a).steps = (u.outputs a).steps := rfl

def ofPoly (w : Computes ea eb f) : Timing (FiniteComputes.ofPoly w) :=
  ⟨w.time,fun a => (w.outputs a).steps_le_m⟩

def width (t : Timing u) : Polynomial ℕ :=
  Polynomial.X+t.bound*Polynomial.C u.machine.primitiveBudget
theorem output_length (t : Timing u) (a : A) :
    (eb.encode (f a)).length≤t.width.eval (ea.encode a).length :=
  t.computes.outputBound.length_le a

/-- Transporting a timed run along equal input/output words and clock bounds
does not change its stored step count. The type equality is the ordinary
dependent transport used by FiniteComputes.congr/recode, not another run. -/
private theorem transported_steps (m : Machine)
    {xs xs' ys ys' : List Bool} {n n' : ℕ}
    (hx : xs=xs') (hy : ys=ys') (hn : n=n')
    (out : TM2OutputsInTime m.computer xs (some ys) n)
    (h : TM2OutputsInTime m.computer xs (some ys) n =
      TM2OutputsInTime m.computer xs' (some ys') n') :
    (Eq.mp h out).steps=out.steps := by
  subst xs'
  subst ys'
  subst n'
  rfl

def congr (t : Timing u) {h : A → B} (he : ∀ a,f a=h a) : Timing (u.congr he) where
  bound := t.bound
  steps_le a := by
    have hs : ((u.congr he).outputs a).steps=(u.outputs a).steps := by
      dsimp only [FiniteComputes.congr]
      exact transported_steps u.machine rfl (congrArg eb.encode (he a)) rfl (u.outputs a) _
    rw [hs]
    exact t.steps_le a

/-- Local second-stage timing is measured in the ORIGINAL first-stage input.
The applications to iterators derive this premise from their actual states. -/
def after (t : Timing u) (Q : Polynomial ℕ)
    (h : ∀ a,(v.outputs (f a)).steps≤Q.eval (ea.encode a).length) : Timing (u.andThen v) where
  bound := t.bound+2*(t.width+1)+Q
  steps_le a := by
    have ha := t.steps_le a
    have hb := h a
    have hw := t.output_length a
    change (v.outputs (f a)).steps+(2*((eb.encode (f a)).length+1)+(u.outputs a).steps)≤_
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega

def andThen (t : Timing u) (s : Timing v) : Timing (u.andThen v) :=
  t.after (s.bound.comp t.width) (fun a => (s.steps_le (f a)).trans (by
    rw [Polynomial.eval_comp]
    exact natPolynomial_eval_mono s.bound (t.output_length a)))

def leftMap (t : Timing u) (ec : Encoding C Bool) : Timing (u.leftMap ec) where
  bound := 2*Polynomial.X+t.bound+2*t.width+6
  steps_le p := by
    have hi : (ea.encode p.1).length≤((pairEncoding ea ec).encode p).length := by
      simp only [pairEncoding_length]; omega
    have ht := (t.steps_le p.1).trans (natPolynomial_eval_mono t.bound hi)
    have hw := (t.output_length p.1).trans (natPolynomial_eval_mono t.width hi)
    change 2*(ea.encode p.1).length+(u.outputs p.1).steps+2*(eb.encode (f p.1)).length+6≤_
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega

def rightMap (s : Timing v) (ea : Encoding A Bool) : Timing (v.rightMap ea) :=
  (((ofPoly (Wiring.swapComputes ea eb)).andThen (s.leftMap ea)).andThen
    (ofPoly (Wiring.swapComputes ec ea))).congr (fun _ => rfl)

def pair {g : A → C} {v : FiniteComputes ea ec g} (t : Timing u) (s : Timing v) :
    Timing (u.pair v) :=
  (((ofPoly (Wiring.diagonalComputes ea)).andThen (t.leftMap ea)).andThen
    (s.rightMap eb)).congr (fun _ => rfl)

def recode (t : Timing u) {h : C → D} (input : C → A)
    (hi : ∀ x,ea.encode (input x)=ec.encode x)
    (ho : ∀ x,eb.encode (f (input x))=ed.encode (h x)) : Timing (u.recode input hi ho) where
  bound := t.bound
  steps_le x := by
    have hs : ((u.recode input hi ho).outputs x).steps=(u.outputs (input x)).steps := by
      dsimp only [FiniteComputes.recode]
      exact transported_steps u.machine (hi x) (ho x)
        (congrArg (fun bits : List Bool => u.time bits.length) (hi x)) (u.outputs (input x)) _
    rw [hs]
    simpa only [hi x] using t.steps_le (input x)

theorem primitive_bound (t : Timing u) (a : A) :
    primitiveCost u.machine (u.outputs a).steps
      (some (initList u.machine.computer (ea.encode a)))≤
      (t.bound*Polynomial.C u.machine.primitiveBudget).eval (ea.encode a).length := by
  simpa using (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ (t.steps_le a))

/-- All temporary stacks, including those internal to normalization, getD
padding, pairing, composition transfer and cleanup, are included. -/
theorem temporary_bits (t : Timing u) (a : A) (i : ℕ) (hi : i≤(u.outputs a).steps)
    (c : u.machine.Config)
    (hc : (fun p => p.bind u.machine.computer.step)^[i]
      (some (initList u.machine.computer (ea.encode a)))=some c) :
    stackSize c.stk≤t.width.eval (ea.encode a).length := by
  have hh := u.machine.run_size_le _ c i hc
  rw [u.machine.size_init] at hh
  have ht := hi.trans (t.steps_le a)
  simpa [width] using hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _)
end
end Timing
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
