import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonSpec

/-! The actual finite Boolean-stack program deriving all three residual fields.
Each original incidence lookup is called once. All projection, fanout, framing,
copying, arithmetic-free tag removal and cleanup costs are charged by the
physical compiler witnesses. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
open Turing Computability BinaryCompose FixedFieldMachines
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option Elab.async false

noncomputable def pinComputes (s b : ℕ) (arity : ℕ → ℕ) (side value : Bool) :
    Computes (inputEncoding s b arity) Frame.wordEncoding
      (fun x => ResidualPinQuery.pinBits side value (cutQuery x)) :=
  (cutComputes s b arity).andThen (ResidualPinQuery.computes s b arity side value)

noncomputable def portComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding
      (fun x => ResidualSurvivorQuery.portBits (survivorQuery x)) :=
  (survivorComputes s b arity).andThen (ResidualSurvivorQuery.computes s b arity)

noncomputable def pairedComputes (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :=
  pairComputes (pinComputes s b arity false a)
    (pairComputes (pinComputes s b arity true z) (portComputes s b arity))

abbrev machine (a z : Bool) : Machine :=
  pairMachine (cutMachine.compose (ResidualPinQuery.machine false a))
    (pairMachine (cutMachine.compose (ResidualPinQuery.machine true z))
      (survivorMachine.compose ResidualSurvivorQuery.machine))

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    Computes (inputEncoding s b arity) Frame.wordEncoding (descriptorBits a z) :=
  recode (pairedComputes s b arity a z) id (fun _ => rfl) (fun x => (descriptor_word a z x).symm)

@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    (computes s b arity a z).machine = machine a z := rfl

noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : Polynomial ℕ :=
  (computes s b arity a z).time

noncomputable def timed (a z : Bool) (x : Input s b arity) :
    TM2OutputsInTime (machine a z).computer ((inputEncoding s b arity).encode x)
      (some (descriptorBits a z x))
      ((timePolynomial s b arity a z).eval ((inputEncoding s b arity).encode x).length) :=
  (computes s b arity a z).outputs x

theorem inFP (a z : Bool) : InFP (inputEncoding s b arity) Frame.wordEncoding (descriptorBits a z) :=
  (computes s b arity a z).inFP

noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : Polynomial ℕ :=
  timePolynomial s b arity a z * Polynomial.C (machine a z).primitiveBudget

theorem primitive_bound (a z : Bool) (x : Input s b arity) :
    FixedFieldMachines.primitiveCost (machine a z) (timed a z x).steps
      (some (initList (machine a z).computer ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity a z).eval ((inputEncoding s b arity).encode x).length := by
  have h := Nat.mul_le_mul_right (machine a z).primitiveBudget (timed a z x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    le_trans (FixedFieldMachines.primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
