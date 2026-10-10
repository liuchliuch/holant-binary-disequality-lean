import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinQueryInterface
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! Actual clean two-endpoint residual descriptor generation. The finite pairing
compiler calls each original endpoint producer once, physically frames both pin
words, and appends the zero-survivor tag. No local pin is supplied as input. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptor
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Input := ResidualPinQuery.Input s b arity

def descriptorBits (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) : List Bool :=
  (ResidualLabel.descriptorEncoding (arity (x.1.val.vertices.get x.2.1).1)).encode
    (ResidualPin.zeroDescriptor x.1.val x.1.property x.2.2 x.2.1 a z)

/-- Literal original-end order: false endpoint first, true endpoint second. -/
theorem descriptor_word (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    descriptorBits a z x = Holant.Algebraic.frame (ResidualPinQuery.pinBits false a x) ++
      (Holant.Algebraic.frame (ResidualPinQuery.pinBits true z x) ++ [false]) := by
  change Holant.Algebraic.frame ((optionEncoding (ResidualLabel.pinEncoding _)).encode
      (ResidualPin.selected a x.1.val x.2.1 (x.1.val.lookup x.1.property (x.2.2,false)))) ++
    (Holant.Algebraic.frame ((optionEncoding (ResidualLabel.pinEncoding _)).encode
      (ResidualPin.selected z x.1.val x.2.1 (x.1.val.lookup x.1.property (x.2.2,true)))) ++ [false]) = _
  rw [ResidualPin.selected_encode,ResidualPin.selected_encode]
  rfl

noncomputable def pairedComputes (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    BinaryCompose.Computes (ResidualPinQuery.inputEncoding s b arity)
      (pairEncoding Frame.wordEncoding (pairEncoding Frame.wordEncoding Frame.wordEncoding))
      (fun x => (ResidualPinQuery.pinBits false a x, ResidualPinQuery.pinBits true z x, [false])) :=
  pairComputes (ResidualPinQuery.computes s b arity false a)
    (pairComputes (ResidualPinQuery.computes s b arity true z)
      (constantComputes (ResidualPinQuery.inputEncoding s b arity) Frame.wordEncoding [false]))

/-- The actual physical machine has only fixed finite control and Boolean tapes. -/
abbrev machine (a z : Bool) : BinaryCompose.Machine :=
  pairMachine (ResidualPinQuery.machine false a)
    (pairMachine (ResidualPinQuery.machine true z) (Constant.machine [false]))

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    BinaryCompose.Computes (ResidualPinQuery.inputEncoding s b arity) Frame.wordEncoding (descriptorBits a z) :=
  recode (pairedComputes s b arity a z) id (fun _ => rfl) (fun x => by
    change Holant.Algebraic.frame (ResidualPinQuery.pinBits false a x) ++
      (Holant.Algebraic.frame (ResidualPinQuery.pinBits true z x) ++ [false]) = descriptorBits a z x
    exact (descriptor_word a z x).symm)

@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    (computes s b arity a z).machine = machine a z := rfl

/-- The composed polynomial explicitly charges fanout, every call, transfer,
framing, constant-tag loading, and cleanup through the proved physical constructors. -/
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : Polynomial ℕ :=
  (computes s b arity a z).time

noncomputable def timed (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    TM2OutputsInTime (machine a z).computer ((ResidualPinQuery.inputEncoding s b arity).encode x)
      (some (descriptorBits a z x)) ((timePolynomial s b arity a z).eval ((ResidualPinQuery.inputEncoding s b arity).encode x).length) :=
  (computes s b arity a z).outputs x

/-- Ordinary polynomial-time computation of the actual residual descriptor bytes. -/
theorem inFP (a z : Bool) :
    InFP (ResidualPinQuery.inputEncoding s b arity) Frame.wordEncoding (descriptorBits a z) :=
  (computes s b arity a z).inFP

noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : Polynomial ℕ :=
  timePolynomial s b arity a z * Polynomial.C (machine a z).primitiveBudget

theorem primitive_bound (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    FixedFieldMachines.primitiveCost (machine a z) (timed a z x).steps
      (some (initList (machine a z).computer ((ResidualPinQuery.inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity a z).eval ((ResidualPinQuery.inputEncoding s b arity).encode x).length := by
  have h := Nat.mul_le_mul_right (machine a z).primitiveBudget (timed a z x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (FixedFieldMachines.primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptor
