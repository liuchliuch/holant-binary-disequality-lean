import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualCoefficientInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptorBounds

/-! Actual original raw/vertex/edge query to the original residual zero
coefficient label. The generated pin descriptor is passed physically into the
stored-signature emitter, retaining input through a proved finite pairing stage. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficient
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Input := ResidualPinQuery.Input s b arity

def prepared (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) : ResidualCoefficientInput.Input s b arity :=
  ⟨x,ResidualPin.zeroDescriptor x.1.val x.1.property x.2.2 x.2.1 a z⟩

def literal (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) : RawClosedNetwork.TreeLabel s b arity :=
  ResidualCoefficientInput.literal s b arity (prepared a z x)

noncomputable def retainComputes (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    BinaryCompose.Computes (ResidualPinQuery.inputEncoding s b arity)
      (ResidualCoefficientInput.inputEncoding s b arity) (prepared a z) :=
  recode (pairComputes (identityComputes (ResidualPinQuery.inputEncoding s b arity))
    (ResidualZeroDescriptor.computes s b arity a z)) id (fun _ => rfl) (fun _ => rfl)

/-- Finite data-only syntax for retention, descriptor generation and original coefficient loading. -/
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : BinaryCompose.Machine :=
  (pairMachine identityMachine (ResidualZeroDescriptor.machine a z)).compose (ResidualCoefficientInput.machine s b arity)

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    BinaryCompose.Computes (ResidualPinQuery.inputEncoding s b arity) (treeLabelEncoding s b arity) (literal a z) :=
  congrComputes ((retainComputes s b arity a z).andThen (ResidualCoefficientInput.computes s b arity)) (fun _ => rfl)

@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    (computes s b arity a z).machine = machine s b arity a z := rfl

noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : Polynomial ℕ :=
  (computes s b arity a z).time

/-- Canonical original coefficient label, from one actual clean whole-machine execution. -/
noncomputable def timed (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    TM2OutputsInTime (machine s b arity a z).computer ((ResidualPinQuery.inputEncoding s b arity).encode x)
      (some ((treeLabelEncoding s b arity).encode (literal a z x)))
      ((timePolynomial s b arity a z).eval ((ResidualPinQuery.inputEncoding s b arity).encode x).length) :=
  (computes s b arity a z).outputs x

theorem inFP (a z : Bool) :
    InFP (ResidualPinQuery.inputEncoding s b arity) (treeLabelEncoding s b arity) (literal a z) :=
  (computes s b arity a z).inFP

noncomputable def originalTimePolynomial (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : Polynomial ℕ :=
  (timePolynomial s b arity a z).comp (5 * (Polynomial.X+1))

/-- Original raw bit length also bounds the retained coordinate fields and every intermediate copy. -/
noncomputable def timed_original (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    TM2OutputsInTime (machine s b arity a z).computer ((ResidualPinQuery.inputEncoding s b arity).encode x)
      (some ((treeLabelEncoding s b arity).encode (literal a z x)))
      ((originalTimePolynomial s b arity a z).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := (timed a z x).steps
  evals_in_steps := (timed a z x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (timePolynomial s b arity a z) (ResidualZeroDescriptor.input_length_le_original x)
    exact le_trans (timed a z x).steps_le_m (by simpa [originalTimePolynomial] using h)

noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : Polynomial ℕ :=
  originalTimePolynomial s b arity a z * Polynomial.C (machine s b arity a z).primitiveBudget

theorem primitive_bound (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    FixedFieldMachines.primitiveCost (machine s b arity a z) (timed_original a z x).steps
      (some (initList (machine s b arity a z).computer ((ResidualPinQuery.inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity a z).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right (machine s b arity a z).primitiveBudget (timed_original a z x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (FixedFieldMachines.primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficient
