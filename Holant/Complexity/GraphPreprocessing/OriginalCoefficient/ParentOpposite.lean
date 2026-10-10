import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionContextInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelectGraph
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentEndpointInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface
import Holant.Complexity.FixedFieldMachines.MachineSyntax
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! A stored original parent row is physically parsed, distributed with the
original edge table and passed to the real opposite-end selector. Roots return
none; original vertex zero remains a distinct successful some-zero result. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentOpposite
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev Base := List (ℕ × ℕ) × Graph.ParentRow
def baseEncoding := pairEncoding EdgeSelect.edgeEncoding ParentRowEncoding.row
def Valid (x : Base) : Prop := match x.2.parent with
  | none => True
  | some q => q.1<x.1.length
instance (x : Base) : Decidable (Valid x) := by unfold Valid; split <;> infer_instance
abbrev Input := {x : Base // Valid x}
def inputEncoding : Encoding Input Bool where
  encode x := baseEncoding.encode x.val
  decode bits := do
    let x ← baseEncoding.decode bits
    if h : Valid x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]

def fieldValue (x : Input) := (x.val.1,x.val.2.parent)
def selected (x : Input) : Option EdgeSelect.Input := match h : x.val.2.parent with
  | none => none
  | some q => some ⟨x.val.1,⟨q.1,by have hp := x.property; simpa [Valid,h] using hp⟩,q.2⟩
theorem selected_none (x : Input) (hp : x.val.2.parent=none) : selected x=none := by
  unfold selected
  split
  · rfl
  · rename_i q he
    rw [hp] at he
    contradiction

theorem selected_some (x : Input) (q : ℕ × Bool) (hp : x.val.2.parent=some q) :
    selected x=some ⟨x.val.1,⟨q.1,by have h := x.property; simpa [Valid,hp] using h⟩,q.2⟩ := by
  unfold selected
  split
  · rename_i he
    rw [hp] at he
    contradiction
  · rename_i q' he
    have hq : q'=q := Option.some.inj (he.symm.trans hp)
    subst q'
    rfl

def value (x : Input) : Option ℕ := (selected x).map EdgeSelect.value
abbrev outputEncoding := optionEncoding UnaryBinary.unaryEncoding

noncomputable def fieldComputes :
    Computes inputEncoding (OptionContext.inputEncoding EdgeSelect.edgeEncoding ParentRowEncoding.endpoint) fieldValue :=
  recode (rightMapComputes EdgeSelect.edgeEncoding ParentEndpoint.computes) Subtype.val (fun _ => rfl)
    (fun x => by cases hp : x.val.2.parent <;> simp [fieldValue,OptionContext.inputEncoding,hp,pairEncoding,ParentRowEncoding.parent,optionEncoding])
noncomputable def prepareComputes : Computes inputEncoding (optionEncoding EdgeSelect.inputEncoding) selected :=
  recode (fieldComputes.andThen (OptionContext.computes EdgeSelect.edgeEncoding ParentRowEncoding.endpoint))
    id (fun _ => rfl) (fun x => by
      cases hp : x.val.2.parent with
      | none =>
        rw [selected_none x hp]
        simp [fieldValue,OptionContext.value,OptionContext.outputEncoding,hp,optionEncoding]
      | some q =>
        rw [selected_some x q hp]
        change (optionEncoding (pairEncoding EdgeSelect.edgeEncoding ParentRowEncoding.endpoint)).encode
          (x.val.2.parent.map (fun q => (x.val.1,q))) = _
        conv_lhs => rw [hp]
        rfl)

abbrev fieldMachine : Machine := rightMapMachine ParentEndpoint.machine
abbrev prepareMachine : Machine := fieldMachine.compose OptionContext.machine
abbrev machine : Machine := prepareMachine.compose (OptionMap.machine EdgeSelect.machine)
noncomputable def computes : Computes inputEncoding outputEncoding value :=
  prepareComputes.andThen (OptionMap.computes EdgeSelect.computes)
@[simp] theorem computes_machine : computes.machine=machine := rfl
noncomputable def timePolynomial : Polynomial ℕ := computes.time
theorem inFP : InFP inputEncoding outputEncoding value := computes.inFP

noncomputable def timed (x : Input) :
    TM2OutputsInTime machine.computer (inputEncoding.encode x) (some (outputEncoding.encode (value x)))
      (timePolynomial.eval (inputEncoding.encode x).length) := computes.outputs x
noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input) :
    primitiveCost machine (timed x).steps (some (initList machine.computer (inputEncoding.encode x))) ≤
      primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

def originalInput (g : Graph) (v : g.Vertex) : Input := ⟨(ReachRound.graphEdges g,g.parentRow v),by
  unfold Valid
  cases hp : (g.parentRow v).parent with
  | none => trivial
  | some q =>
    obtain ⟨e,he,_,_⟩ := g.parentRow_some_spec v q hp
    simpa [ReachRound.graphEdges,←he] using e.isLt⟩

theorem original_none (g : Graph) (v : g.Vertex) (hp : (g.parentRow v).parent=none) :
    value (originalInput g v)=none := by
  rw [value,selected_none (originalInput g v) hp]
  rfl

theorem original_some (g : Graph) (v : g.Vertex) (e : g.Edge) (side : Bool)
    (hp : (g.parentRow v).parent=some (e.val,side)) :
    value (originalInput g v)=some (g.endpoint e (!side)).val := by
  have hs : selected (originalInput g v)=some (EdgeSelect.graphInput g e side) := by
    rw [selected_some (originalInput g v) (e.val,side) hp]
    rfl
  rw [value,hs,Option.map_some,EdgeSelect.graph_value]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentOpposite
