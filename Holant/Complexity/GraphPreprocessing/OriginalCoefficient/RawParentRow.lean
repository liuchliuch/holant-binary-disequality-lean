import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentQueryWiring
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParentGraph
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentLabel

/-! A canonical parent row directly from raw closed-network bytes and one
original vertex. Count, edge table, component root, first-hit depth and original
parent end are all physically computed by the composed finite machines. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentRow
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev Input := RawRootReach.Input
abbrev inputEncoding := RawRootReach.inputEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}

def tableTarget (x : Input s b arity) : (List Bool × List Bool) × List Bool :=
  (RawRootReach.tableData x.1,List.replicate x.2.val true)
noncomputable def tableComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) ParentQueryWiring.tableTarget tableTarget :=
  recode (leftMapComputes Frame.wordEncoding (RawRootReach.tableComputes s b arity))
    (fun x => (x.1,List.replicate x.2.val true)) (fun _ => rfl) (fun _ => rfl)

def dataEncoding := pairEncoding UnaryBinary.unaryEncoding ParentQueryWiring.tableTarget
def dataValue (x : Input s b arity) := (RawComponentLabel.value x,tableTarget x)
noncomputable def dataComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) dataEncoding dataValue :=
  pairComputes (RawComponentLabel.computes s b arity) (tableComputes s b arity)

def prepared (x : Input s b arity) : ℕ × RootedParent.Input :=
  (RawComponentLabel.value x,RootedParent.originalQuery (x.1.val.graph x.1.property) x.2)
def preparedEncoding := pairEncoding UnaryBinary.unaryEncoding RootedParent.inputEncoding

noncomputable def wireComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) preparedEncoding prepared :=
  recode ((dataComputes s b arity).andThen
    (recode ParentQueryWiring.computes
      (fun x : ℕ × ((List Bool × List Bool) × List Bool) => (List.replicate x.1 true,x.2))
      (fun _ => rfl) (fun _ => rfl))) id (fun _ => rfl) (fun _ => rfl)

def value (x : Input s b arity) : Holant.OneHot.Computable.Graph.ParentRow :=
  (x.1.val.graph x.1.property).parentRow x.2
abbrev dataMachine : Machine := pairMachine RawComponentLabel.machine (LeftMap.machine RawEdgeTable.machine)
abbrev prepareMachine : Machine := dataMachine.compose ParentQueryWiring.machine
abbrev machine : Machine := prepareMachine.compose (rightMapMachine RootedParent.machine)

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) ParentRowEncoding.row value :=
  recode ((wireComputes s b arity).andThen (rightMapComputes UnaryBinary.unaryEncoding RootedParent.computes))
    id (fun _ => rfl) (fun x => by
      change Holant.Algebraic.frame (List.replicate (RawComponentLabel.value x) true)++
        RootedParent.outputEncoding.encode (RootedParent.value (RootedParent.originalQuery (x.1.val.graph x.1.property) x.2)) = _
      rw [RootedParent.original_value]
      rfl)

@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine := rfl
noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ := (computes s b arity).time
noncomputable def timed (x : Input s b arity) :
    TM2OutputsInTime machine.computer ((inputEncoding s b arity).encode x) (some (ParentRowEncoding.row.encode (value x)))
      ((timePolynomial s b arity).eval ((inputEncoding s b arity).encode x).length) := (computes s b arity).outputs x

theorem inFP : InFP (inputEncoding s b arity) ParentRowEncoding.row value := (computes s b arity).inFP
noncomputable def originalTimePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (timePolynomial s b arity).comp (3*(Polynomial.X+1))
noncomputable def timed_original (x : Input s b arity) :
    TM2OutputsInTime machine.computer ((inputEncoding s b arity).encode x) (some (ParentRowEncoding.row.encode (value x)))
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

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentRow
