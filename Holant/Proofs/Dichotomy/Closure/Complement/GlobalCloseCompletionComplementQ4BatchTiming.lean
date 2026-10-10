import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4BatchBounds
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4IterationTiming

/-! Polynomial bounds for the exact pre/fold/post runs on the actual native
oracle transcript. All coefficient, root, sample and loop budgets are proved
from the original source bytes; no running-time premise is exported. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4BatchTiming
open Turing Computability Holant Holant.Algebraic Holant.Complexity Holant.OneHot
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
namespace B
export GlobalCloseCompletionComplementQ4Batch
  (Input inputEncoding oldTables roots target pre answered initial resultState result prepareComputes finishComputes post)
end B
namespace A
export GlobalCloseCompletionComplementQ4BatchBounds
  (coordinates coeff unit neg degreePolynomial listPolynomial rootPolynomial valuePolynomial scalarPolynomial
   count_bound root_length roots_budget target_budget initial_values initial_length initial_denominator)
end A
namespace I
export GlobalCloseCompletionComplementQ4IterationMachine (finite stateEncoding)
end I
namespace T
export GlobalCloseCompletionComplementQ4IterationTiming (timePolynomial steps)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {degree s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (a i.val))
variable (N : NativeAntiTargetSource.Output H 4) (v : Fin 4→K) (support : Bool) (j : Fin 4)

def transcript : Polynomial ℕ:=OracleBatch.decoderBound (B.pre F H N v support j) ((B.oldTables F H).outputBound F)
def preparedBound : Polynomial ℕ:=(B.prepareComputes F support).outputBound.bound.comp (transcript F H N v support j)
def iterationTime : Polynomial ℕ:=T.timePolynomial F (A.coordinates F H v)
  A.degreePolynomial A.listPolynomial A.rootPolynomial (A.valuePolynomial F H N v support j)
    A.scalarPolynomial A.scalarPolynomial
def iteratedBound : Polynomial ℕ:=preparedBound F H N v support j+
  iterationTime F H N v support j*Polynomial.C (I.finite F).machine.primitiveBudget
def arithmeticTime : Polynomial ℕ:=iterationTime F H N v support j+2*(iteratedBound F H N v support j+1)+
  (B.finishComputes F support).time.comp (iteratedBound F H N v support j)
def postTime : Polynomial ℕ:=(B.prepareComputes F support).time.comp (transcript F H N v support j)+
  2*(preparedBound F H N v support j+1)+arithmeticTime F H N v support j

theorem answered_length (x : B.Input H N) :
    ((GlobalCloseCompletionComplementQ4Batch.answerEncoding F).encode (B.answered F H N v support j x)).length≤
      (transcript F H N v support j).eval ((B.inputEncoding H N).encode x).length:=
  OracleBatch.decoder_length_le (B.pre F H N v support j) ((B.oldTables F H).outputBound F) x

theorem initial_length (x : B.Input H N) :
    ((Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.ReverseFold.inputEncoding F.encoding (I.stateEncoding F)).encode
      (B.initial F H N v support j x)).length≤
      (preparedBound F H N v support j).eval ((B.inputEncoding H N).encode x).length := by
  exact (B.prepareComputes F support).outputBound.length_le (B.answered F H N v support j x) |>.trans
    (by simpa only [preparedBound,Polynomial.eval_comp] using
      natPolynomial_eval_mono (B.prepareComputes F support).outputBound.bound (answered_length F H N v support j x))

theorem iteration_steps (x : B.Input H N) :
    ((I.finite F).outputs (B.initial F H N v support j x)).steps≤
      (iterationTime F H N v support j).eval ((B.inputEncoding H N).encode x).length := by
  have hm:=A.count_bound H N x
  have hd : (B.roots H N v support j x).length≤A.degreePolynomial.eval ((B.inputEncoding H N).encode x).length := by
    rw [A.root_length]
    simpa [A.degreePolynomial] using Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 4
  have hl : (B.initial F H N v support j x).2.1.length≤A.listPolynomial.eval ((B.inputEncoding H N).encode x).length := by
    rw [A.initial_length]
    simpa only [A.listPolynomial,Polynomial.eval_add,Polynomial.eval_one,A.root_length] using Nat.add_le_add_right hd 1
  exact T.steps F (A.coordinates F H v) (.inl 5) (.inl 4) (A.unit F H v) (A.neg F H v)
    _ _ _ _ _ _ _ _ _ _ _ hd hl (A.roots_budget F H N v support j x)
      (A.initial_values F H N v support j x) (A.target_budget F H N v support j x)
      (A.initial_denominator F H N v support j x)

def iteration_outputs (x : B.Input H N) :
    TM2OutputsInTime (I.finite F).machine.computer
      ((Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.ReverseFold.inputEncoding F.encoding (I.stateEncoding F)).encode
        (B.initial F H N v support j x))
      (some ((I.stateEncoding F).encode (B.resultState F H N v support j x)))
      ((iterationTime F H N v support j).eval ((B.inputEncoding H N).encode x).length) where
  steps:=((I.finite F).outputs (B.initial F H N v support j x)).steps
  evals_in_steps:=((I.finite F).outputs (B.initial F H N v support j x)).evals_in_steps
  steps_le_m:=iteration_steps F H N v support j x

theorem result_length (x : B.Input H N) :
    ((I.stateEncoding F).encode (B.resultState F H N v support j x)).length≤
      (iteratedBound F H N v support j).eval ((B.inputEncoding H N).encode x).length := by
  have h:=(I.finite F).machine.output_length_le _ _ _ (iteration_outputs F H N v support j x)
  have hi:=initial_length F H N v support j x
  simp only [iteratedBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  exact h.trans (Nat.add_le_add_right hi _)

def arithmetic_outputs (x : B.Input H N) :
    TM2OutputsInTime ((I.finite F).machine.compose (B.finishComputes F support).machine).computer
      ((Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.ReverseFold.inputEncoding F.encoding (I.stateEncoding F)).encode
        (B.initial F H N v support j x))
      (some (F.encoding.encode (B.result F H N v support j x)))
      ((arithmeticTime F H N v support j).eval ((B.inputEncoding H N).encode x).length) := by
  let first:=iteration_outputs F H N v support j x
  let last:=(B.finishComputes F support).outputs (B.resultState F H N v support j x)
  let all:=Machine.compose_correct (I.finite F).machine (B.finishComputes F support).machine _ _ _ _ _ first last
  refine {steps:=all.steps,evals_in_steps:=all.evals_in_steps,steps_le_m:=?_}
  have ht:=all.steps_le_m
  have hs:=result_length F H N v support j x
  have hf:=natPolynomial_eval_mono (B.finishComputes F support).time hs
  simp only [arithmeticTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_comp]
  omega

def post_outputs (x : B.Input H N) :
    TM2OutputsInTime (B.post F support).computer
      ((GlobalCloseCompletionComplementQ4Batch.answerEncoding F).encode (B.answered F H N v support j x))
      (some (F.encoding.encode (B.result F H N v support j x)))
      ((postTime F H N v support j).eval ((B.inputEncoding H N).encode x).length) := by
  let first:=(B.prepareComputes F support).outputs (B.answered F H N v support j x)
  let last:=arithmetic_outputs F H N v support j x
  let all:=Machine.compose_correct (B.prepareComputes F support).machine
    ((I.finite F).machine.compose (B.finishComputes F support).machine) _ _ _ _ _ first last
  refine {steps:=all.steps,evals_in_steps:=all.evals_in_steps,steps_le_m:=?_}
  have ht:=all.steps_le_m
  have hs:=initial_length F H N v support j x
  dsimp only [B.initial] at hs
  have hp:=natPolynomial_eval_mono (B.prepareComputes F support).time (answered_length F H N v support j x)
  simp only [postTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_comp]
  omega


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4BatchTiming
end
