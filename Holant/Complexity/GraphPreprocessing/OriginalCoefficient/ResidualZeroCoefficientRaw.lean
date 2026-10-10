import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficient
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroDescriptorRaw

/-! Exact executable projection and full reset observer for the original-query
to residual coefficient pipeline. No alternate denotation evaluator is used. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 200000
set_option Elab.async false

def raw (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : RawMachine :=
  ((RawMachine.erase identityMachine).pair (ResidualZeroDescriptor.raw a z)).compose
    (RawMachine.erase (ResidualCoefficientInput.machine s b arity))

theorem erase_machine (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    RawMachine.erase (machine s b arity a z) = raw s b arity a z := by
  let left := pairMachine identityMachine (ResidualZeroDescriptor.machine a z)
  let right := ResidualCoefficientInput.machine s b arity
  have h := RawMachine.erase_compose left right
  have hp := RawMachine.erase_pair identityMachine (ResidualZeroDescriptor.machine a z)
  have hd := congrArg (RawMachine.pair (RawMachine.erase identityMachine)) (ResidualZeroDescriptor.erase_machine a z)
  exact h.trans (congrArg (fun m => RawMachine.compose m (RawMachine.erase right)) (hp.trans hd))

theorem step_eq (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    HEq (raw s b arity a z).view.step (machine s b arity a z).computer.step :=
  RawMachine.step_of_erase_eq _ _ (erase_machine s b arity a z)

theorem start_eq (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    HEq (raw s b arity a z).view.start (initList (machine s b arity a z).computer) :=
  RawMachine.start_of_erase_eq _ _ (erase_machine s b arity a z)

theorem observer_eq (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) :
    letI : Fintype (machine s b arity a z).K := (machine s b arity a z).finiteK
    letI : DecidableEq (machine s b arity a z).K := (machine s b arity a z).decidableK
    HEq (raw s b arity a z).view.observeHalt
      (fun c : (machine s b arity a z).Config => (c.stk (machine s b arity a z).output,
        decide (∀ k, k ≠ (machine s b arity a z).output → c.stk k = []))) :=
  RawMachine.observer_of_erase_eq _ _ (erase_machine s b arity a z)

def identityCheck : RationalArithmetic.StateCheck (RawMachine.erase identityMachine) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq Unit))

def coefficientCheck (s b : ℕ) (arity : ℕ → ℕ) :
    RationalArithmetic.StateCheck (RawMachine.erase (ResidualCoefficientInput.machine s b arity)) :=
  @RationalArithmetic.StateCheck.ofEq _ (inferInstanceAs (DecidableEq (Option Bool × Unit)))

def reset (s b : ℕ) (arity : ℕ → ℕ) (a z : Bool) : RationalArithmetic.StateCheck (raw s b arity a z) :=
  (identityCheck.pair (ResidualZeroDescriptor.reset a z)).compose (coefficientCheck s b arity)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficient
