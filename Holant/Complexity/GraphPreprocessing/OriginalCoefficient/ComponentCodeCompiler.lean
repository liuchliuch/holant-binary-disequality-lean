import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.JoinedResidualCompiler

/-! Actual raw component classification and selective finite compilation. The
value explicitly names the two established residual branches; the final literal
GraphCode identification is transported separately by canonical interchange. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentCodeCompiler
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
def canonicalValue (x : RawComponentInputs.Input s b arity) : Code (RawClosedNetwork.TreeLabel s b arity) :=
  ((RawComponentInputs.selectTree x).map RawComponentCompiler.canonicalValue).getD
    (((RawComponentInputs.selectCycle x).map JoinedResidualCompiler.value).getD [.zero])
noncomputable def treeWords (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawComponentCompiler.canonicalEncoding s b arity) Frame.wordEncoding
      (fun x => (codeEncoding (treeLabelEncoding s b arity)).encode (RawComponentCompiler.canonicalValue x)) :=
  recode (RawComponentCompiler.canonicalComputes s b arity) id (fun _ => rfl) (fun _ => rfl)
noncomputable def cycleWords (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawComponentInputs.cycleEncoding s b arity) Frame.wordEncoding
      (fun x => (codeEncoding (treeLabelEncoding s b arity)).encode (JoinedResidualCompiler.value x)) :=
  recode (JoinedResidualCompiler.computes s b arity) id (fun _ => rfl) (fun _ => rfl)
noncomputable def dispatchComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawComponentInputs.preparedEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) canonicalValue :=
  recode (BranchDriver.computes ((codeEncoding (treeLabelEncoding s b arity)).encode [.zero])
    (RawComponentInputs.treeComputes s b arity) (RawComponentInputs.cycleComputes s b arity)
    (treeWords s b arity) (cycleWords s b arity)) id (fun _ => rfl) (fun x => by
      cases ht : RawComponentInputs.selectTree x <;> cases hc : RawComponentInputs.selectCycle x <;>
        simp [BranchDriver.value,canonicalValue,ht,hc,Frame.wordEncoding])
noncomputable def canonicalComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawComponentCompiler.canonicalEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) canonicalValue :=
  (RawComponentInputs.prepareComputes s b arity).andThen (dispatchComputes s b arity)
def value (x : RawRootReach.Input s b arity) := canonicalValue (RawComponentCompiler.normalized x)
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) value :=
  (RawComponentCompiler.normalizeComputes s b arity).andThen (canonicalComputes s b arity)
abbrev dispatchMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  BranchDriver.machine ((codeEncoding (treeLabelEncoding s b arity)).encode [.zero])
    (ComponentOption.machine false) (ComponentOption.machine true)
    (RawTreeCompiler.machine s b arity) (JoinedResidualCompiler.machine s b arity)
abbrev canonicalMachine (s b : ℕ) (arity : ℕ → ℕ) := RawComponentInputs.prepareMachine.compose (dispatchMachine s b arity)
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) := RawComponentCompiler.normalizeMachine.compose (canonicalMachine s b arity)
@[simp] theorem dispatch_machine (s b : ℕ) (arity : ℕ → ℕ) : (dispatchComputes s b arity).machine=dispatchMachine s b arity := rfl
@[simp] theorem canonical_machine (s b : ℕ) (arity : ℕ → ℕ) : (canonicalComputes s b arity).machine=canonicalMachine s b arity := rfl
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (RawRootReach.inputEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) value := (computes s b arity).inFP
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (computes s b arity).time.comp (3*(Polynomial.X+1))
noncomputable def timed (x : RawRootReach.Input s b arity) :
    TM2OutputsInTime (machine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x)
      (some ((codeEncoding (treeLabelEncoding s b arity)).encode (value x)))
      ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := ((computes s b arity).outputs x).steps
  evals_in_steps := ((computes s b arity).outputs x).evals_in_steps
  steps_le_m := le_trans ((computes s b arity).outputs x).steps_le_m
    (by simpa [timePolynomial] using natPolynomial_eval_mono (computes s b arity).time (RawRootReach.input_length_le_original x))
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := timePolynomial s b arity*Polynomial.C (machine s b arity).primitiveBudget
theorem primitive_bound (x : RawRootReach.Input s b arity) :
    primitiveCost (machine s b arity) (timed x).steps (some (initList (machine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x)))≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right (machine s b arity).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ComponentCodeCompiler
