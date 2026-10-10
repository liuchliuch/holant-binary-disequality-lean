import Holant.Complexity.FixedFieldMachines.Inverse
import Holant.OneHot.StackProgram.Machine.Unbox
import Holant.OneHot.StackProgram.Machine.Operator
import Holant.Complexity.BinaryCompose.Composition

/-! Finish the interpolation stack with one genuine variable field division,
then emit the unchanged canonical fieldword. Both input values and the computed
output length are charged through existing machine bounds. -/
namespace Holant.Complexity.BinaryInterpolation.DivisionStack
open Turing Computability BinaryCompose FixedFieldMachines Holant.Algebraic
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
set_option backward.isDefEq.respectTransparency false

def encoding (F : FixedField K n) : Encoding (K×K) Bool where
  encode p := (stackEncoding F.encoding).encode [p.1,p.2]
  decode bits := ((stackEncoding F.encoding).decode bits).bind fun l =>
    match l with
    | [a,b] => some (a,b)
    | _ => none
  decode_encode p := by simp

theorem encoding_length (F : FixedField K n) (p : K×K) :
    ((encoding F).encode p).length=2*(F.encoding.encode p.1).length+
      2*(F.encoding.encode p.2).length+5 := by
  simp [encoding,stackEncoding,framedListEncoding,framedListEncode,frame_length]
  omega

def widthPolynomial (F : FixedField K n) : Polynomial ℕ :=
  Polynomial.X+(fieldDivisionComputes F).outputBound.bound.comp (3*Polynomial.X+1)

def timePolynomial (F : FixedField K n) : Polynomial ℕ :=
  (fieldDivisionComputes F).time.comp (3*widthPolynomial F+1)+20*widthPolynomial F+31

def computes (F : FixedField K n) : Computes (encoding F) F.encoding (fun p : K×K => p.1/p.2) where
  machine := (Operator.machine (fieldDivisionComputes F).machine).compose Unbox.machine
  time := timePolynomial F
  outputs p := by
    let L := ((encoding F).encode p).length
    let W := (widthPolynomial F).eval L
    have hl := encoding_length F p
    have hL : (F.encoding.encode p.1).length≤L ∧ (F.encoding.encode p.2).length≤L := by
      dsimp [L];omega
    have hW : L≤W := by simp [W,widthPolynomial]
    have hp : ((pairEncoding F.encoding F.encoding).encode p).length≤3*L+1 := by
      rw [pairEncoding_length];omega
    have hz : (F.encoding.encode (p.1/p.2)).length≤W := by
      have hs := (fieldDivisionComputes F).outputBound.length_le p
      have hm := natPolynomial_eval_mono (fieldDivisionComputes F).outputBound.bound hp
      dsimp [W]
      simp only [widthPolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_comp,
        Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
      omega
    let first := Operator.provider_timed F.encoding (fun q : K×K => q.1/q.2)
      (fieldDivisionComputes F) p.1 p.2 [] W (hL.1.trans hW) (hL.2.trans hW) hz
    have last := Unbox.encoded F.encoding (p.1/p.2)
    have all := BinaryCompose.Machine.compose_run
      (Operator.machine (fieldDivisionComputes F).machine) Unbox.machine
      ((encoding F).encode p) ((stackEncoding F.encoding).encode [p.1/p.2])
      (F.encoding.encode (p.1/p.2)) first.steps (2*(F.encoding.encode (p.1/p.2)).length+5)
      first.evals_in_steps last
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    have ht := first.steps_le_m
    have hout : ((stackEncoding F.encoding).encode [p.1/p.2]).length=
        2*(F.encoding.encode (p.1/p.2)).length+3 := by
      simp [stackEncoding,framedListEncoding,framedListEncode,frame_length]
    rw [hout]
    change _≤(timePolynomial F).eval L
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp,Polynomial.eval_one]
    change _≤(fieldDivisionComputes F).time.eval (3*W+1)+20*W+31
    omega

end
end Holant.Complexity.BinaryInterpolation.DivisionStack
