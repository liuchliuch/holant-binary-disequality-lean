import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentOpposite
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionAny
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordCompare

/-! An actual child predicate: original stored parent-end lookup, physical
unary word equality, and finite optional-Boolean collapse. A root row cannot
match original vertex zero merely because its parent payload is empty. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildPredicate
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev Input := ℕ × ParentOpposite.Input
def inputEncoding := pairEncoding UnaryBinary.unaryEncoding ParentOpposite.inputEncoding
def comparison (p : ℕ × ℕ) : Bool := decide (p.1=p.2)
noncomputable def comparisonComputes :
    Computes (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding) encodingBoolBool comparison :=
  recode WordCompare.computes (fun p => (List.replicate p.1 true,List.replicate p.2 true)) (fun _ => rfl)
    (fun p => by simp [WordCompare.value,comparison,List.replicate_inj])

def prepared (x : Input) : Option (ℕ × ℕ) := (ParentOpposite.value x.2).map (fun v => (x.1,v))
noncomputable def prepareComputes :
    Computes inputEncoding (optionEncoding (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)) prepared :=
  (rightMapComputes UnaryBinary.unaryEncoding ParentOpposite.computes).andThen
    (OptionContext.computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
def value (x : Input) : Bool := decide (ParentOpposite.value x.2=some x.1)

abbrev prepareMachine : Machine := (rightMapMachine ParentOpposite.machine).compose OptionContext.machine
abbrev machine : Machine := (prepareMachine.compose (OptionMap.machine WordCompare.machine)).compose OptionAny.machine
noncomputable def computes : Computes inputEncoding encodingBoolBool value :=
  congrComputes ((prepareComputes.andThen (OptionMap.computes comparisonComputes)).andThen OptionAny.computes)
    (fun x => by cases hp : ParentOpposite.value x.2 <;> simp [prepared,comparison,OptionAny.value,value,hp,eq_comm])
@[simp] theorem computes_machine : computes.machine=machine := rfl
noncomputable def timePolynomial : Polynomial ℕ := computes.time
theorem inFP : InFP inputEncoding encodingBoolBool value := computes.inFP
noncomputable def timed (x : Input) :
    TM2OutputsInTime machine.computer (inputEncoding.encode x) (some (encodingBoolBool.encode (value x)))
      (timePolynomial.eval (inputEncoding.encode x).length) := computes.outputs x
noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input) :
    primitiveCost machine (timed x).steps (some (initList machine.computer (inputEncoding.encode x))) ≤
      primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

def graphInput (g : Graph) (target child : g.Vertex) : Input := (target.val,ParentOpposite.originalInput g child)

theorem root_false (g : Graph) (target child : g.Vertex) (hp : (g.parentRow child).parent=none) :
    value (graphInput g target child)=false := by
  change decide (ParentOpposite.value (ParentOpposite.originalInput g child)=some target.val)=false
  rw [ParentOpposite.original_none g child hp]
  rfl

theorem original_edge (g : Graph) (target child : g.Vertex) (e : g.Edge) (side : Bool)
    (hp : (g.parentRow child).parent=some (e.val,side)) :
    value (graphInput g target child)=decide (g.endpoint e (!side)=target) := by
  change decide (ParentOpposite.value (ParentOpposite.originalInput g child)=some target.val)=_
  rw [ParentOpposite.original_some g child e side hp]
  simp [Fin.ext_iff]
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildPredicate
