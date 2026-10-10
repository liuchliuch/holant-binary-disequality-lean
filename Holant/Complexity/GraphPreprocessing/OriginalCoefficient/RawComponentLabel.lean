import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawRootReach
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.FirstTrueGraph

/-! A clean original component label from raw network bytes and one unary
original vertex ID. The actual endpoint extraction and bounded BFS execute
before the physical least-bit scan. No prepared labels or parent table enter. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabel
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev Input := RawRootReach.Input
abbrev inputEncoding := RawRootReach.inputEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}

def reached (x : Input s b arity) : FirstTrue.Input :=
  FirstTrue.graphInput (x.1.val.graph x.1.property) x.2

def value (x : Input s b arity) : ℕ := ((x.1.val.graph x.1.property).label x.2).val

noncomputable def reachComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) FirstTrue.inputEncoding reached :=
  recode (RawRootReach.computes s b arity) id (fun _ => rfl) (fun _ => rfl)

abbrev machine : Machine := RawRootReach.machine.compose FirstTrue.machine
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) UnaryBinary.unaryEncoding value :=
  congrComputes ((reachComputes s b arity).andThen FirstTrue.computes)
    (fun x => FirstTrue.graph_value (x.1.val.graph x.1.property) x.2)

@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine := rfl
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time
noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime machine.computer ((inputEncoding s b arity).encode x)
      (some (List.replicate (value x) true))
      ((timePolynomial s b arity).eval ((inputEncoding s b arity).encode x).length) := (computes s b arity).outputs x

theorem inFP : InFP (inputEncoding s b arity) UnaryBinary.unaryEncoding value := (computes s b arity).inFP

noncomputable def originalTimePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (timePolynomial s b arity).comp (3*(Polynomial.X+1))
noncomputable def timed_original (x : Input s b arity) :
    TM2OutputsInTime machine.computer ((inputEncoding s b arity).encode x)
      (some (List.replicate (value x) true))
      ((originalTimePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := (timed x).steps
  evals_in_steps := (timed x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (timePolynomial s b arity) (RawRootReach.input_length_le_original x)
    exact le_trans (timed x).steps_le_m (by simpa [originalTimePolynomial] using h)

noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  originalTimePolynomial s b arity*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input s b arity) :
    primitiveCost machine (timed_original x).steps (some (initList machine.computer ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed_original x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

theorem output_length_lt (x : Input s b arity) : (List.replicate (value x) true).length < x.1.val.vertices.length := by
  simpa only [List.length_replicate,value,RawClosedNetwork.graph] using ((x.1.val.graph x.1.property).label x.2).isLt

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabel
