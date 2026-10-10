import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.OptionCell

set_option autoImplicit false

/-! Kernel-checked recovery component. Actual recovered rational bytes emit a new equality
q*x_j=p by the existing matrix compiler; dimensions and original fields are
retained. The successor port is formed by physical unary equality/succ.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing Codec
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
noncomputable section
def successorIndex (q : CoordinateQuery) : Fin q.1.val.dimension :=
  if h : q.2.val+1=q.1.val.dimension then ⟨0,by have hj := q.2.isLt; omega⟩
  else ⟨q.2.val+1,by have hj := q.2.isLt; omega⟩
theorem successorIndex_value (q : CoordinateQuery) : (successorIndex q).val =
    if q.2.val+1=q.1.val.dimension then 0 else q.2.val+1 := by
  by_cases h : q.2.val+1=q.1.val.dimension
  · unfold successorIndex
    rw [dif_pos h, if_pos h]
  · unfold successorIndex
    rw [dif_neg h, if_neg h]
def Context.next (c : Context) (r : ℚ) : Context :=
  let f := c.fix r
  ⟨f.original,⟨f.current.1,successorIndex f.current⟩,f.sameDimension,f.sourceSize⟩
namespace FixProgram
noncomputable section
abbrev Query := Context × ℚ
def encoding := pairEncoding contextEncoding rationalEncoding
def context : Computes encoding contextEncoding (fun q : Query => q.1) := Wiring.firstComputes _ _
def scalar : Computes encoding rationalEncoding (fun q : Query => q.2) := Wiring.secondComputes _ _
def numerator : Computes encoding encodingNatBool (fun q : Query => q.2.num.toNat) :=
  (scalar.andThen RationalArithmetic.numeratorComputes).andThen RoundingProgram.toNat
def denominator : Computes encoding encodingNatBool (fun q : Query => q.2.den) :=
  scalar.andThen RationalArithmetic.denominatorComputes
def fixedInput : Computes encoding inputEncoding (fun q : Query => (q.1.fix q.2).current.1) :=
  (pairComputes (context.andThen ContextProgram.current) (pairComputes numerator denominator)).andThen
    ExactPointRecovery.ThresholdProgram.validatedFixedComputes
def index : Computes encoding GraphPreprocessing.UnaryBinary.unaryEncoding
    (fun q : Query => q.1.current.2.val) :=
  context.andThen (ContextProgram.current.andThen ExactPointRecovery.ThresholdProgram.coordinateIndex)
def dimension : Computes encoding GraphPreprocessing.UnaryBinary.unaryEncoding
    (fun q : Query => q.1.current.1.val.dimension) :=
  context.andThen (ContextProgram.currentRaw.andThen Parsing.dimension)
def nextIndex : Computes encoding GraphPreprocessing.UnaryBinary.unaryEncoding
    (fun q : Query => (successorIndex (q.1.fix q.2).current).val) :=
  congrComputes (ifComputes
    ((pairComputes (index.andThen WireLists.succComputes) dimension).andThen Parsing.unaryEqual)
    (constantComputes encoding GraphPreprocessing.UnaryBinary.unaryEncoding 0)
    (index.andThen WireLists.succComputes)) (fun q => by
      simp [successorIndex_value,Context.fix,
        ExactPointRecovery.ThresholdProgram.fixedValue,ExactPointRecovery.ThresholdProgram.rawFixed])
def nextCoordinate : Computes encoding coordinateEncoding
    (fun q : Query => (q.1.next q.2).current) :=
  recode (pairComputes fixedInput nextIndex) id (fun _ => rfl) (fun _ => rfl)
def computes : Computes encoding contextEncoding (fun q : Query => q.1.next q.2) :=
  recode (pairComputes (context.andThen ContextProgram.original) nextCoordinate) id
    (fun _ => rfl) (fun _ => rfl)
end
end FixProgram
theorem next_supporting (c : Context) (r : ℚ) (hr : 0≤r) (hc : Supporting c)
    (hm : ∀ y, Feasible c.current.1.val y → r≤y c.current.2) : Supporting (c.next r) := by
  change Supporting (c.fix r)
  exact fix_supporting c r hr hc hm
theorem next_feasible (c : Context) (r : ℚ) (hr : 0≤r) (x : Fin c.current.1.val.dimension → ℚ) :
    Feasible (c.next r).current.1.val x ↔ Feasible c.current.1.val x ∧ x c.current.2=r := by
  simpa only [Context.next] using fix_feasible c r hr x
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
