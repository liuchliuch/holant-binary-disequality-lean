import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapRun
import Holant.OneHot.StackProgram.GraphLabelEncoding
import Holant.Complexity.FixedFieldMachines.PrimitiveCost
import Holant.Complexity.GraphPreprocessing.FrameMachine

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false
variable {A : Type} {B : A → Type} (ea : Encoding A Bool) (eb : ∀ a, Encoding (B a) Bool)
variable (f : (Σ a,B a) → List Bool)
variable (w : Computes (sigmaEncoding ea eb) Frame.wordEncoding f)

def inputEncoding : Encoding (Σ a,List (B a)) Bool := sigmaEncoding ea (fun a => framedListEncoding (eb a))
def value (x : Σ a,List (B a)) : List Bool := x.2.flatMap (fun b => f ⟨x.1,b⟩)

theorem member_length {C : Type} (e : Encoding C Bool) (xs : List C) (a : C) (ha : a∈xs) :
    (e.encode a).length≤(framedListEncode e xs).length := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with h|h
    · subst b
      simp only [framedListEncode,List.length_cons,List.length_append,Holant.Algebraic.frame_length]
      omega
    · have ht := ih h
      simp only [framedListEncode,List.length_cons,List.length_append,Holant.Algebraic.frame_length]
      omega

theorem input_bounds (x : Σ a,List (B a)) :
    (ea.encode x.1).length≤((inputEncoding ea eb).encode x).length ∧
    x.2.length≤((inputEncoding ea eb).encode x).length ∧
    ∀ b∈x.2, ((sigmaEncoding ea eb).encode ⟨x.1,b⟩).length≤((inputEncoding ea eb).encode x).length ∧
      ((eb x.1).encode b).length≤((inputEncoding ea eb).encode x).length := by
  have hc := framedListEncode_length_lower (eb x.1) x.2
  have hi : ((inputEncoding ea eb).encode x).length=2*(ea.encode x.1).length+1+(framedListEncode (eb x.1) x.2).length := by
    simp only [inputEncoding,sigmaEncoding,List.length_append,Holant.Algebraic.frame_length,framedListEncoding]
  refine ⟨by omega,by omega,?_⟩
  intro b hb
  have hm := member_length (eb x.1) x.2 b hb
  have hq : ((sigmaEncoding ea eb).encode ⟨x.1,b⟩).length=2*(ea.encode x.1).length+1+((eb x.1).encode b).length := by
    simp only [sigmaEncoding,List.length_append,Holant.Algebraic.frame_length]
  exact ⟨by omega,by omega⟩

noncomputable def roundPolynomial : Polynomial ℕ := w.time+w.outputBound.bound+6*Polynomial.X+9
noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.X*roundPolynomial ea eb f w+3*Polynomial.X+Polynomial.X*w.outputBound.bound+7

theorem ticks_bound {C : Type} (e : Encoding C Bool) (context : List Bool) (g : C → List Bool) (steps : C → ℕ)
    (xs : List C) (P : ℕ)
    (h : ∀ a∈xs, steps a+4*context.length+2*(e.encode a).length+(g a).length+9≤P) :
    ticks e context g steps xs≤xs.length*P := by
  induction xs with
  | nil => simp [ticks]
  | cons a xs ih =>
    have hh := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [ticks,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    omega
theorem flat_length_bound {C : Type} (g : C → List Bool) (xs : List C) (P : ℕ)
    (h : ∀ a∈xs, (g a).length≤P) : (xs.flatMap g).length≤xs.length*P := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hh := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

noncomputable def timed (x : Σ a,List (B a)) :
    TM2OutputsInTime (machine w.machine).computer ((inputEncoding ea eb).encode x)
      (some (value f x)) ((timePolynomial ea eb f w).eval ((inputEncoding ea eb).encode x).length) where
  steps := ticks (eb x.1) (ea.encode x.1) (fun b => f ⟨x.1,b⟩) (fun b => (w.outputs ⟨x.1,b⟩).steps) x.2+
    3*(ea.encode x.1).length+(value f x).length+7
  evals_in_steps := whole w.machine (eb x.1) (ea.encode x.1) (fun b => f ⟨x.1,b⟩)
    (fun b => (w.outputs ⟨x.1,b⟩).steps) x.2 (fun b _ => (w.outputs ⟨x.1,b⟩).evals_in_steps)
  steps_le_m := by
    let N := ((inputEncoding ea eb).encode x).length
    obtain ⟨hc,hn,hb⟩ := input_bounds ea eb x
    have output_bound (b : B x.1) (hm : b∈x.2) : (f ⟨x.1,b⟩).length≤w.outputBound.bound.eval N := by
      exact le_trans (w.outputBound.length_le ⟨x.1,b⟩) (natPolynomial_eval_mono w.outputBound.bound (hb b hm).1)
    have ht := ticks_bound (eb x.1) (ea.encode x.1) (fun b => f ⟨x.1,b⟩)
      (fun b => (w.outputs ⟨x.1,b⟩).steps) x.2 ((roundPolynomial ea eb f w).eval N) (by
        intro b hm
        have hs := le_trans (w.outputs ⟨x.1,b⟩).steps_le_m (natPolynomial_eval_mono w.time (hb b hm).1)
        have ho := output_bound b hm
        have hl := (hb b hm).2
        simp only [roundPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
        dsimp only [N] at *
        omega)
    have ho := flat_length_bound (fun b => f ⟨x.1,b⟩) x.2 (w.outputBound.bound.eval N) output_bound
    have htc := Nat.mul_le_mul_right ((roundPolynomial ea eb f w).eval N) hn
    have hoc := Nat.mul_le_mul_right (w.outputBound.bound.eval N) hn
    change _≤(timePolynomial ea eb f w).eval N
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    change (ticks _ _ _ _ _)+3*(ea.encode x.1).length+(x.2.flatMap (fun b => f ⟨x.1,b⟩)).length+7≤_
    dsimp only [N] at *
    omega

noncomputable def computes : Computes (inputEncoding ea eb) Frame.wordEncoding (value f) where
  machine := machine w.machine
  time := timePolynomial ea eb f w
  outputs := timed ea eb f w
include w in
theorem inFP : InFP (inputEncoding ea eb) Frame.wordEncoding (value f) := (computes ea eb f w).inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
