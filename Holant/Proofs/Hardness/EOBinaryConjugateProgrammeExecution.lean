import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeLoop

/-! Physical initialization, finite iteration, and canonical final division.
This execution theorem is specialized by the graph programme to its actual
oracle answers. It never assumes an evaluator, runtime, or completed trace. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeLoop
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K A : Type} [Field K] [Algebra ℚ K] [Fintype A] {n : ℕ}
variable (F : FixedField K n)

def frameState : Computes (S.encoding F) (inputEncoding F) id :=
  recode ((encodeComputes (S.encoding F)).andThen frameComputes) id (fun _=>rfl) (fun _=>rfl)

def finishMachine := (machine F).compose (S.finishComputes F).machine

def arithmetic := (frameState F).machine.compose (finishMachine F)

def result (s : S.State K) : K := (value F s).numerator/(value F s).divisor

variable (base : A→Fin n→ℚ) (R U V L : Polynomial ℕ)

def finishTime : Polynomial ℕ := timePolynomial F base R U V L+
  2*width F base R U V L+2+(S.finishComputes F).time.comp (width F base R U V L)

def arithmeticTime : Polynomial ℕ :=
  (frameState F).time.comp L+4*L+4+finishTime F base R U V L

variable (unit minus : A) (hunit : F.decode (base unit)=1) (hminus : F.decode (base minus) = -1)

include unit minus hunit hminus in
def loop_outputs (N : ℕ) (s : S.State K)
    (h : S.Bounded (fun a=>F.decode (base a)) (R.eval N) (U.eval N) (V.eval N) s)
    (hs : (S.encoding F |>.encode s).length≤L.eval N) :
    TM2OutputsInTime (machine F).computer ((inputEncoding F).encode s)
      (some ((S.encoding F).encode (value F s))) ((timePolynomial F base R U V L).eval N) := by
  let hr := whole_run F base R U V L unit minus hunit hminus N s h hs
  exact {steps:=hr.choose,steps_le_m:=hr.choose_spec.1,evals_in_steps:=hr.choose_spec.2}

include unit minus hunit hminus in
def finish_outputs (N : ℕ) (s : S.State K)
    (h : S.Bounded (fun a=>F.decode (base a)) (R.eval N) (U.eval N) (V.eval N) s)
    (hs : (S.encoding F |>.encode s).length≤L.eval N) :
    TM2OutputsInTime (finishMachine F).computer ((inputEncoding F).encode s)
      (some (F.encoding.encode (result F s))) ((finishTime F base R U V L).eval N) := by
  let first := loop_outputs F base R U V L unit minus hunit hminus N s h hs
  let last := (S.finishComputes F).outputs (value F s)
  let all := Machine.compose_correct (machine F) (S.finishComputes F).machine _ _ _ _ _ first last
  refine {steps:=all.steps,evals_in_steps:=all.evals_in_steps,steps_le_m:=?_}
  have ht := all.steps_le_m
  simp only [id_eq] at ht
  have hw := iterate_width F base R U V L unit minus hunit hminus N s h hs
    ((S.encoding F).encode s).length hs
  change ((S.encoding F).encode (value F s)).length≤_ at hw
  have hf := natPolynomial_eval_mono (S.finishComputes F).time hw
  simp only [finishTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

include unit minus hunit hminus in
def arithmetic_outputs (N : ℕ) (s : S.State K)
    (h : S.Bounded (fun a=>F.decode (base a)) (R.eval N) (U.eval N) (V.eval N) s)
    (hs : (S.encoding F |>.encode s).length≤L.eval N) :
    TM2OutputsInTime (arithmetic F).computer ((S.encoding F).encode s)
      (some (F.encoding.encode (result F s))) ((arithmeticTime F base R U V L).eval N) := by
  let first := (frameState F).outputs s
  let last := finish_outputs F base R U V L unit minus hunit hminus N s h hs
  let all := Machine.compose_correct (frameState F).machine (finishMachine F) _ _ _ _ _ first last
  refine {steps:=all.steps,evals_in_steps:=all.evals_in_steps,steps_le_m:=?_}
  have ht := all.steps_le_m
  simp only [id_eq] at ht
  have hf := natPolynomial_eval_mono (frameState F).time hs
  have hb : ((inputEncoding F).encode s).length=2*((S.encoding F).encode s).length+1 := by
    simp [inputEncoding]
  simp only [arithmeticTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeLoop
