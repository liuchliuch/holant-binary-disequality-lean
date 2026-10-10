import Holant.Complexity.GraphPreprocessing.ComponentSelection.ParentMatches
import Holant.Complexity.GraphPreprocessing.ComponentSelection.RootEntry
import Holant.Complexity.GraphPreprocessing.ComponentSelection.Semantics
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentRowSelectInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicate
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildren

/-! The surplus predicate reads the actual original edge, then only its two
endpoint rows. All IDs remain unary physical words. The context invariant only
certifies valid indices and has no representation on the tapes. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection.EndpointPredicate
open Turing Computability BinaryCompose FixedFieldMachines OriginalCoefficient
open Holant.OneHot.Computable Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev Data := (List (ℕ × ℕ) × List Graph.ParentRow) × ℕ
def dataEncoding := pairEncoding RawChildren.contextEncoding UnaryBinary.unaryEncoding
def Valid (c : Data) : Prop := ∀ p∈c.1.1,p.1<c.1.2.length ∧ p.2<c.1.2.length
instance (c : Data) : Decidable (Valid c) := inferInstanceAs (Decidable (∀ p∈_,_ ∧ _))
abbrev Context := {c : Data // Valid c}
def contextEncoding : Encoding Context Bool where
  encode c := dataEncoding.encode c.val
  decode word := do
    let c ← dataEncoding.decode word
    if h : Valid c then some ⟨c,h⟩ else none
  decode_encode c := by simp [c.property]
abbrev Input := Σ c : Context, Fin c.val.1.1.length
def inputEncoding := sigmaEncoding contextEncoding (fun c => OccurrenceLabel.unaryPortEncoding c.val.1.1.length)
def project (x : Input) : Data × ℕ := (x.1.val,x.2.val)
def baseEncoding := pairEncoding dataEncoding UnaryBinary.unaryEncoding

noncomputable def tablesComputes : Computes baseEncoding RawChildren.contextEncoding (fun x => x.1.1) :=
  (Wiring.firstComputes dataEncoding UnaryBinary.unaryEncoding).andThen
    (Wiring.firstComputes RawChildren.contextEncoding UnaryBinary.unaryEncoding)
noncomputable def edgesComputes : Computes inputEncoding EdgeSelect.edgeEncoding (fun x => x.1.val.1.1) :=
  recode (tablesComputes.andThen (Wiring.firstComputes EdgeSelect.edgeEncoding ParentRowEncoding.table)) project
    (fun _ => rfl) (fun _ => rfl)
noncomputable def rowsComputes : Computes inputEncoding ParentRowEncoding.table (fun x => x.1.val.1.2) :=
  recode (tablesComputes.andThen (Wiring.secondComputes EdgeSelect.edgeEncoding ParentRowEncoding.table)) project
    (fun _ => rfl) (fun _ => rfl)
noncomputable def rootComputes : Computes inputEncoding UnaryBinary.unaryEncoding (fun x => x.1.val.2) :=
  recode ((Wiring.firstComputes dataEncoding UnaryBinary.unaryEncoding).andThen
    (Wiring.secondComputes RawChildren.contextEncoding UnaryBinary.unaryEncoding)) project (fun _ => rfl) (fun _ => rfl)
noncomputable def indexComputes : Computes inputEncoding UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes dataEncoding UnaryBinary.unaryEncoding) project (fun _ => rfl) (fun _ => rfl)
def endpointQuery (side : Bool) (x : Input) : EdgeSelect.Input := ⟨x.1.val.1.1,x.2,!side⟩
def endpoint (side : Bool) (x : Input) : ℕ := EdgeSelect.value (endpointQuery side x)
noncomputable def endpointQueryComputes (side : Bool) : Computes inputEncoding EdgeSelect.inputEncoding (endpointQuery side) :=
  recode (pairComputes edgesComputes (pairComputes indexComputes
    (constantComputes inputEncoding ParentRowEncoding.orientation (!side)))) id (fun _ => rfl) (fun _ => rfl)
noncomputable def endpointComputes (side : Bool) : Computes inputEncoding UnaryBinary.unaryEncoding (endpoint side) :=
  (endpointQueryComputes side).andThen EdgeSelect.computes
theorem endpoint_lt (side : Bool) (x : Input) : endpoint side x<x.1.val.1.2.length := by
  have h := x.1.property (x.1.val.1.1.get x.2) (List.get_mem _ _)
  cases side with
  | false => exact h.1
  | true => exact h.2
def rowQuery (side : Bool) (x : Input) : ParentRowSelect.Input Graph.ParentRow :=
  ⟨x.1.val.1.2,⟨endpoint side x,endpoint_lt side x⟩⟩
def row (side : Bool) (x : Input) : Graph.ParentRow := ParentRowSelect.selected (rowQuery side x)
noncomputable def rowQueryComputes (side : Bool) : Computes inputEncoding (ParentRowSelect.inputEncoding ParentRowEncoding.row) (rowQuery side) :=
  recode (pairComputes rowsComputes (endpointComputes side)) id (fun _ => rfl) (fun _ => rfl)
noncomputable def rowComputes (side : Bool) : Computes inputEncoding ParentRowEncoding.row (row side) :=
  (rowQueryComputes side).andThen (ParentRowSelect.computes ParentRowEncoding.row)
def parentMatches (side : Bool) (x : Input) := ParentMatches.value (x.2.val,row side x)
noncomputable def matchesComputes (side : Bool) : Computes inputEncoding encodingBoolBool (parentMatches side) :=
  (pairComputes indexComputes (rowComputes side)).andThen ParentMatches.computes
def used (x : Input) := parentMatches false x || parentMatches true x
def disjunction (p : Bool × Bool) := p.1 || p.2
noncomputable def orComputes : Computes NeighborPredicate.boolPair encodingBoolBool disjunction :=
  FiniteRecode.computes _ _ _ 4 NeighborPredicate.bool_length
noncomputable def usedComputes : Computes inputEncoding encodingBoolBool used :=
  (pairComputes (matchesComputes false) (matchesComputes true)).andThen orComputes
def sameComponent (x : Input) := decide (x.1.val.2=(row false x).component)
noncomputable def componentComputes : Computes inputEncoding UnaryBinary.unaryEncoding (fun x => (row false x).component) :=
  recode ((rowComputes false).andThen RootEntry.componentComputes) id (fun _ => rfl) (fun _ => rfl)
noncomputable def sameComputes : Computes inputEncoding encodingBoolBool sameComponent :=
  (pairComputes rootComputes componentComputes).andThen ChildPredicate.comparisonComputes
def eligible (p : Bool × Bool) := p.1 && !p.2
noncomputable def eligibleComputes : Computes NeighborPredicate.boolPair encodingBoolBool eligible :=
  FiniteRecode.computes _ _ _ 4 NeighborPredicate.bool_length
def value (x : Input) : Bool := sameComponent x && !used x
noncomputable def computes : Computes inputEncoding encodingBoolBool value :=
  (pairComputes sameComputes usedComputes).andThen eligibleComputes

abbrev tablesMachine : Machine := Wiring.firstMachine.compose Wiring.firstMachine
abbrev edgesMachine : Machine := tablesMachine.compose Wiring.firstMachine
abbrev rowsMachine : Machine := tablesMachine.compose secondMachine
abbrev rootMachine : Machine := Wiring.firstMachine.compose secondMachine
abbrev endpointQueryMachine (side : Bool) : Machine := pairMachine edgesMachine (pairMachine secondMachine (Constant.machine [!side]))
abbrev endpointMachine (side : Bool) : Machine := (endpointQueryMachine side).compose EdgeSelect.machine
abbrev rowQueryMachine (side : Bool) : Machine := pairMachine rowsMachine (endpointMachine side)
abbrev rowMachine (side : Bool) : Machine := (rowQueryMachine side).compose ParentRowSelect.machine
abbrev matchesMachine (side : Bool) : Machine := (pairMachine secondMachine (rowMachine side)).compose ParentMatches.machine
abbrev orMachine : Machine := FiniteRecode.machine NeighborPredicate.boolPair encodingBoolBool disjunction 4
abbrev usedMachine : Machine := (pairMachine (matchesMachine false) (matchesMachine true)).compose orMachine
abbrev componentMachine : Machine := (rowMachine false).compose Wiring.firstMachine
abbrev sameMachine : Machine := (pairMachine rootMachine componentMachine).compose WordCompare.machine
abbrev eligibleMachine : Machine := FiniteRecode.machine NeighborPredicate.boolPair encodingBoolBool eligible 4
abbrev machine : Machine := (pairMachine sameMachine usedMachine).compose eligibleMachine
@[simp] theorem computes_machine : computes.machine=machine := rfl
theorem inFP : InFP inputEncoding encodingBoolBool value := computes.inFP

def originalContext (g : Graph) (root : g.Vertex) : Context :=
  ⟨((ReachRound.graphEdges g,g.parentTable),root.val),by
    intro p hp
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
    simpa using And.intro q.1.isLt q.2.isLt⟩
def originalInput (g : Graph) (root : g.Vertex) (e : g.Edge) : Input :=
  ⟨originalContext g root,⟨e.val,by simpa [originalContext,ReachRound.graphEdges] using e.isLt⟩⟩
theorem endpoint_original (g : Graph) (root : g.Vertex) (e : g.Edge) (side : Bool) :
    endpoint side (originalInput g root e)=(g.endpoint e side).val := by
  have h := EdgeSelect.graph_value g e (!side)
  change EdgeSelect.value (EdgeSelect.graphInput g e (!side))=_
  simpa only [Bool.not_not] using h
theorem row_original (g : Graph) (root : g.Vertex) (e : g.Edge) (side : Bool) :
    row side (originalInput g root e)=g.parentRow (g.endpoint e side) := by
  unfold row rowQuery ParentRowSelect.selected
  have hi := endpoint_original g root e side
  have idx : (⟨endpoint side (originalInput g root e),endpoint_lt side (originalInput g root e)⟩ :
      Fin g.parentTable.length)=Fin.cast g.parentTable_length.symm (g.endpoint e side) := Fin.ext hi
  change g.parentTable.get _=_
  rw [idx,ParentRowEncoding.original_row]
theorem original_value (g : Graph) (root : g.Vertex) (e : g.Edge) :
    value (originalInput g root e)=(decide (g.label (g.endpoint e false)=root) && !edgeUsed g e) := by
  simp only [value,sameComponent,used,parentMatches,ParentMatches.value,row_original,Graph.parentRow_component,
    edgeUsed]
  have he : (originalInput g root e).2.val=e.val := rfl
  have hr : (originalInput g root e).1.val.2=root.val := rfl
  rw [he,hr]
  have hc : decide (root.val=(g.label (g.endpoint e false)).val)=decide (g.label (g.endpoint e false)=root) := by
    apply decide_eq_decide.mpr
    simp only [Fin.ext_iff,eq_comm]
  rw [hc]
end Holant.Complexity.GraphPreprocessing.ComponentSelection.EndpointPredicate
