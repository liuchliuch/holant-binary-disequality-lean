import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficientBounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentEndpointInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EndpointQuery
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentRow

/-! The stored canonical parent endpoint is physically parsed and serialized,
then used at either original end to emit an ordinary singleton coefficient.
The original target vertex remains explicit, allowing the same machine to emit
the child's b coefficient and its parent's port coefficient. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev Base (s b : ℕ) (arity : ℕ → ℕ) := RawRootReach.Input s b arity × Graph.ParentRow
def Valid (x : Base s b arity) : Prop := ∀ q ∈ x.2.parent, q.1<x.1.1.val.edges.length
instance (x : Base s b arity) : Decidable (Valid x) := inferInstanceAs (Decidable (∀ q ∈ x.2.parent, _))
abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := {x : Base s b arity // Valid x}
def baseEncoding (s b : ℕ) (arity : ℕ → ℕ) := pairEncoding (RawRootReach.inputEncoding s b arity) ParentRowEncoding.row
def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool where
  encode x := (baseEncoding s b arity).encode x.val
  decode bits := do
    let x ← (baseEncoding s b arity).decode bits
    if h : Valid x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]

def side (flip bit : Bool) := if flip then !bit else bit
def parent (flip : Bool) (x : Input s b arity) : Option (Fin x.val.1.1.val.edges.length × Bool) :=
  x.val.2.parent.attach.map (fun q => (⟨q.val.1,x.property q.val q.property⟩,side flip q.val.2))
def entry (flip : Bool) (x : Input s b arity) : OrdinaryCoefficient.Input s b arity :=
  ⟨x.val.1.1,x.val.1.2,parent flip x⟩
def value (flip : Bool) (x : Input s b arity) := OrdinaryCoefficient.value (entry flip x)

noncomputable def sideComputes (flip : Bool) : Computes encodingBoolBool encodingBoolBool (side flip) :=
  FiniteRecode.computes encodingBoolBool encodingBoolBool (side flip) 1 (fun bit => by cases bit <;> exact Nat.le_refl 1)
abbrev sideMachine (flip : Bool) := FiniteRecode.machine encodingBoolBool encodingBoolBool (side flip) 1
noncomputable def endpointComputes (flip : Bool) :
    Computes ParentRowEncoding.endpoint RawClosedNetwork.endpointEncoding (fun q => (q.1,side flip q.2)) :=
  recode (EndpointQuery.computes.andThen
    (rightMapComputes encodingNatBool (sideComputes flip))) id (fun _ => rfl) (fun _ => rfl)

noncomputable def rowComputes (flip : Bool) :
    Computes ParentRowEncoding.row (optionEncoding RawClosedNetwork.endpointEncoding)
      (fun row => row.parent.map (fun q => (q.1,side flip q.2))) :=
  (recode (ed := optionEncoding ParentRowEncoding.endpoint) (g := Graph.ParentRow.parent)
    ParentEndpoint.computes id (fun _ => rfl) (fun row => by cases hp : row.parent <;> simp [hp,ParentRowEncoding.parent,optionEncoding])).andThen (OptionMap.computes (endpointComputes flip))

def words := pairEncoding Frame.wordEncoding Frame.wordEncoding
def wireInputEncoding := pairEncoding words Frame.wordEncoding
def wireOutputEncoding := pairEncoding Frame.wordEncoding words
noncomputable def rawWire : Computes wireInputEncoding Frame.wordEncoding (fun x => x.1.1) :=
  (Wiring.firstComputes words Frame.wordEncoding).andThen (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def vertexWire : Computes wireInputEncoding Frame.wordEncoding (fun x => x.1.2) :=
  (Wiring.firstComputes words Frame.wordEncoding).andThen (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def wireComputes : Computes wireInputEncoding wireOutputEncoding (fun x => (x.1.1,(x.1.2,x.2))) :=
  pairComputes rawWire (pairComputes vertexWire (Wiring.secondComputes words Frame.wordEncoding))

theorem parent_word (flip : Bool) (x : Input s b arity) :
    (optionEncoding RawClosedNetwork.endpointEncoding).encode
      (x.val.2.parent.map (fun q => (q.1,side flip q.2))) =
    (optionEncoding (pairEncoding (SignatureLabel.binaryFinEncoding x.val.1.1.val.edges.length)
      ParentRowEncoding.orientation)).encode (parent flip x) := by
  cases hp : x.val.2.parent <;> simp [parent,hp,optionEncoding,Option.attach,ParentRowEncoding.orientation]
  rfl

noncomputable def prepareComputes (flip : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (OrdinaryCoefficient.inputEncoding s b arity) (entry flip) :=
  recode ((rightMapComputes (RawRootReach.inputEncoding s b arity) (rowComputes flip)).andThen
    (recode wireComputes
      (fun x => ((RawClosedNetwork.encoding.encode x.1.1.val,List.replicate x.1.2.val true),
        (optionEncoding RawClosedNetwork.endpointEncoding).encode x.2)) (fun _ => rfl) (fun _ => rfl)))
    Subtype.val (fun _ => rfl) (fun x => by
      change Holant.Algebraic.frame _++(Holant.Algebraic.frame _++
        (optionEncoding RawClosedNetwork.endpointEncoding).encode _) = _
      rw [parent_word]
      rfl)

noncomputable def computes (flip : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (treeLabelEncoding s b arity) (value flip) :=
  (prepareComputes flip s b arity).andThen (OrdinaryCoefficient.computes s b arity)

abbrev endpointMachine (flip : Bool) : Machine := EndpointQuery.machine.compose (rightMapMachine (sideMachine flip))
abbrev rowMachine (flip : Bool) : Machine := ParentEndpoint.machine.compose (OptionMap.machine (endpointMachine flip))
abbrev rawWireMachine : Machine := Wiring.firstMachine.compose Wiring.firstMachine
abbrev vertexWireMachine : Machine := Wiring.firstMachine.compose secondMachine
abbrev wireMachine : Machine := pairMachine rawWireMachine (pairMachine vertexWireMachine secondMachine)
abbrev prepareMachine (flip : Bool) : Machine := (rightMapMachine (rowMachine flip)).compose wireMachine
abbrev machine (flip : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Machine :=
  (prepareMachine flip).compose (OrdinaryCoefficient.machine s b arity)
@[simp] theorem computes_machine (flip : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    (computes flip s b arity).machine=machine flip s b arity := rfl
theorem inFP (flip : Bool) : InFP (inputEncoding s b arity) (treeLabelEncoding s b arity) (value flip) :=
  (computes flip s b arity).inFP

def originalInput (x : RawRootReach.Input s b arity) : Input s b arity :=
  ⟨(x,RawParentRow.value x),by
    intro q hp
    obtain ⟨e,he,_,_⟩ := (x.1.val.graph x.1.property).parentRow_some_spec x.2 q hp
    have hh := e.isLt
    rw [he] at hh
    simpa only [RawClosedNetwork.graph,List.length_ofFn] using hh⟩
noncomputable def originalPrepare (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) (inputEncoding s b arity) originalInput :=
  recode (pairComputes (identityComputes (RawRootReach.inputEncoding s b arity))
    (RawParentRow.computes s b arity)) id (fun _ => rfl) (fun _ => rfl)
noncomputable def originalComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) (treeLabelEncoding s b arity)
      (fun x => value false (originalInput x)) :=
  (originalPrepare s b arity).andThen (computes false s b arity)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient
