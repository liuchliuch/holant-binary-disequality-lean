import Holant.Proofs.Algorithms.TransformRecognition.RationalProductTemplateMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalProductTemplateSource
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open RationalProductTemplateMachine
variable {n v : ℕ}

def edgeCode (e : Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Edge n) :
    RationalProductTemplateMachine.Edge := ((e.1.1.val,e.1.2.val),e.2)
def fromSource (edges : List (Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Edge n))
    (address : Parameter n → Fin v) (x : Fin n → Bool) : Input :=
  (v,edges.map edgeCode,(address none).val,
    List.ofFn (fun j => ((address (some (j,false))).val,(address (some (j,true))).val)),List.ofFn x)

theorem checkEdge_source (e : Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Edge n)
    (x : Fin n → Bool) :
    checkEdge (List.ofFn x,edgeCode e)=SparseProductTemplate.edgeCheck e x := by
  simp only [checkEdge,edgeCode,Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn,
    SparseProductTemplate.edgeCheck]

theorem holds_source (edges : List (Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Edge n))
    (address : Parameter n → Fin v) (x : Fin n → Bool) :
    holds (fromSource edges address x)=SparseProductTemplate.holdsCheck edges x := by
  simp only [RationalProductTemplateMachine.holds,fromSource,List.all_map,Function.comp_def,checkEdge_source,SparseProductTemplate.holdsCheck]

theorem unary_source (edges : List (Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Edge n))
    (address : Parameter n → Fin v) (x : Fin n → Bool) (j : Fin n) :
    unaryAddress (fromSource edges address x) j.val=(address (some (j,x j))).val := by
  simp only [unaryAddress,fromSource,Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn]
  cases x j <;> rfl

theorem factors_source (edges : List (Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Edge n))
    (address : Parameter n → Fin v) (x : Fin n → Bool) :
    factors (fromSource edges address x)=
      (List.ofFn (fun j => SparseTransform.variableCode RationalCompiler.data (address (some (j,x j))))).map
        RationalInputMachine.rowWire := by
  unfold factors
  simp only [fromSource,List.length_ofFn]
  change CommonFieldMachine.Coordinates.tab n
    (fun j => RationalSparseMachine.variable v (unaryAddress (fromSource edges address x) j)) = _
  rw [CommonFieldMachine.Coordinates.tab_ofFn,List.map_ofFn]
  congr 1
  funext j
  rw [unary_source,RationalSparseMachine.variable_wire]
  rfl

theorem value_source (edges : List (Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Edge n))
    (address : Parameter n → Fin v) (x : Fin n → Bool) :
    value (fromSource edges address x)=RationalInputMachine.rowWire
      (SparseProductTemplate.entry RationalCompiler.data edges address x) := by
  unfold value
  rw [holds_source,factors_source]
  change (if SparseProductTemplate.holdsCheck edges x then
    RationalSparseMachine.mul (RationalSparseMachine.variable v (address none).val)
      (RationalSparseMachine.product v _) else []) = _
  rw [RationalSparseMachine.variable_wire,RationalSparseMachine.product_wire]
  by_cases hh : SparseProductTemplate.holdsCheck edges x=true
  · simp only [hh,ite_true,SparseProductTemplate.entry,RationalSparseMachine.mul_wire]
  · simp [hh,SparseProductTemplate.entry,RationalInputMachine.rowWire]

noncomputable def outputs (edges : List (Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Edge n))
    (address : Parameter n → Fin v) (x : Fin n → Bool) :
    TM2OutputsInTime executes.machine.computer (encoding.encode (fromSource edges address x))
      (some (RationalSparseMachine.encoding.encode (RationalInputMachine.rowWire
        (SparseProductTemplate.entry RationalCompiler.data edges address x))))
      (executes.cost (fromSource edges address x)) := by
  have h := executes.outputs (fromSource edges address x)
  rw [value_source] at h
  exact h
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalProductTemplateSource
