import Holant.Proofs.LinearProgramming.Support.Infrastructure.Timing

/-!
Exact bitmap-iterator retiming, including the existing frame serializer,
prepare, per-round context copy/call/cleanup and final output transfer. The old
FiniteComputes.time/grow recurrence is never used in a polynomial estimate.
The state bounds supplied to the local lemmas below are proved from input data
in Inner and StateBounds before constructing any exported timing witness.
-/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.Iteration
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
noncomputable section
variable {A : Type} {ea : Encoding A Bool} {next : A → A}
  {w : FiniteComputes ea ea next}

def provider (t : Timing w) : Timing (Iterate.provider ea next w) :=
  (Timing.ofPoly (Wiring.firstComputes ea Frame.wordEncoding)).andThen t
def round (t : Timing w) (W : Polynomial ℕ) : Polynomial ℕ :=
  (provider t).bound.comp (2*W+1)+7*W+11
def core (t : Timing w) (W : Polynomial ℕ) : Polynomial ℕ :=
  5*W+8+W*round t W+2*W+5
def frameProgram (ea : Encoding A Bool) : Computes ea (Iterate.wrapped ea) id :=
  recode ((encodeComputes ea).andThen frameComputes) id (fun _ => rfl) (fun _ => rfl)
def total (t : Timing w) (W : Polynomial ℕ) : Polynomial ℕ :=
  (frameProgram ea).time.comp W+2*(2*W+2)+core t W

theorem ticks_le (t : Timing w) (W : Polynomial ℕ) (s : A) (N : ℕ)
    (hs : ∀ i,(ea.encode ((next^[i]) s)).length≤W.eval N) (k i : ℕ) :
    Iterate.ticks ea next w ((next^[i]) s) k≤k*(round t W).eval N := by
  induction k generalizing i with
  | zero => simp [Iterate.ticks]
  | succ k ih =>
    let a := (next^[i]) s
    let b := next a
    let h := (Iterate.provider ea next w).outputs (a,([] : List Bool))
    have ha : (ea.encode a).length≤W.eval N := hs i
    have hb := hs (i+1)
    have he : b=(next^[i+1]) s := by simp [b,a,Function.iterate_succ_apply']
    have hp : h.steps≤(provider t).bound.eval (2*W.eval N+1) := by
      apply ((provider t).steps_le (a,([] : List Bool))).trans
      apply natPolynomial_eval_mono
      rw [pairEncoding_length]
      change 2*(ea.encode a).length+1≤2*W.eval N+1
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 ha) 1
    have hr : h.steps+5*(ea.encode a).length+2*(ea.encode b).length+11≤(round t W).eval N := by
      rw [he]
      simp only [round,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_comp,Polynomial.eval_one]
      omega
    have ht := ih (i+1)
    rw [← he] at ht
    change Iterate.ticks ea next w b k+h.steps+5*(ea.encode a).length+
      2*(ea.encode b).length+11≤_
    nlinarith

theorem wrapped_steps (t : Timing w) (W : Polynomial ℕ) (s : A) (N : ℕ)
    (hs : ∀ i,(ea.encode ((next^[i]) s)).length≤W.eval N) :
    ((Iterate.wrappedComputes ea next w).outputs s).steps≤(core t W).eval N := by
  let L := (ea.encode s).length
  have hL : L≤W.eval N := hs 0
  have hf := hs L
  have ht := ticks_le t W s N hs L 0
  have hm := Nat.mul_le_mul_right ((round t W).eval N) hL
  change (2*(ea.encode ((next^[L]) s)).length+5)+
    (Iterate.ticks ea next w s L+(5*L+8))≤_
  change Iterate.ticks ea next w s L≤L*(round t W).eval N at ht
  simp only [core,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

theorem steps (t : Timing w) (W : Polynomial ℕ) (s : A) (N : ℕ)
    (hs : ∀ i,(ea.encode ((next^[i]) s)).length≤W.eval N) :
    ((Iterate.computes ea next w).outputs s).steps≤(total t W).eval N := by
  have h0 : (ea.encode s).length≤W.eval N := hs 0
  have hf := ((frameProgram ea).outputs s).steps_le_m.trans
    (natPolynomial_eval_mono (frameProgram ea).time h0)
  have hc := wrapped_steps t W s N hs
  change ((Iterate.wrappedComputes ea next w).outputs s).steps+
    (2*((frame (ea.encode s)).length+1)+((frameProgram ea).outputs s).steps)≤_
  rw [frame_length]
  simp only [total,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_ofNat]
  omega
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.Iteration
