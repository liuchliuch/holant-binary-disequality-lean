import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredWiring
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParentCoefficientSpec
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficientMeaning

/-! A stored original parent row and original cut ID to the literal conditioned
coefficient. The parent field is physically parsed/serialized and optionally
flipped, then the real two-pin/surviving-port provider runs on original data. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredCoefficient
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev Data (s b : ℕ) (arity : ℕ → ℕ) := Σ x : ParentCoefficient.Input s b arity, Fin x.val.1.1.val.edges.length
def Valid (x : Data s b arity) : Prop := ∀ q∈x.1.val.2.parent,q.1≠x.2.val
instance (x : Data s b arity) : Decidable (Valid x) := inferInstanceAs (Decidable (∀ q∈x.1.val.2.parent,_))
abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := {x : Data s b arity // Valid x}
def dataEncoding (s b : ℕ) (arity : ℕ → ℕ) :=
  sigmaEncoding (ParentCoefficient.inputEncoding s b arity) (fun x => SignatureLabel.binaryFinEncoding x.val.1.1.val.edges.length)
def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool where
  encode x := (dataEncoding s b arity).encode x.val
  decode bits := do
    let x ← (dataEncoding s b arity).decode bits
    if h : Valid x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]

theorem parent_origin (flip : Bool) (x : ParentCoefficient.Input s b arity)
    (q : Fin x.val.1.1.val.edges.length × Bool) (hq : q∈ParentCoefficient.parent flip x) :
    ∃ p∈x.val.2.parent,p.1=q.1.val := by
  cases hp : x.val.2.parent with
  | none => rw [ParentCoefficient.parent_none flip x hp] at hq; contradiction
  | some p =>
    rw [ParentCoefficient.parent_some flip x p hp] at hq
    refine ⟨p,rfl,?_⟩
    exact congrArg (fun z : Fin x.val.1.1.val.edges.length × Bool => z.1.val) (Option.some.inj hq)

def prepared (flip : Bool) (x : Input s b arity) : ResidualParent.Input s b arity :=
  ⟨⟨x.val.1.val.1.1,x.val.1.val.1.2,x.val.2,ParentCoefficient.parent flip x.val.1⟩,by
    intro q hq
    obtain ⟨p,hp,he⟩ := parent_origin flip x.val.1 q hq
    intro hc
    apply x.property p hp
    exact he.trans (congrArg Fin.val hc).symm⟩
def words (x : OrdinaryCoefficient.Input s b arity × List Bool) :=
  ((RawClosedNetwork.encoding.encode x.1.1.val,(List.replicate x.1.2.1.val true,
    (optionEncoding (pairEncoding (SignatureLabel.binaryFinEncoding x.1.1.val.edges.length) ParentRowEncoding.orientation)).encode x.1.2.2)),x.2)
noncomputable def prepareComputes (flip : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ResidualParent.inputEncoding s b arity) (prepared flip) :=
  recode ((leftMapComputes Frame.wordEncoding (ParentCoefficient.prepareComputes flip s b arity)).andThen
    (recode ResidualStoredWiring.computes words (fun _ => rfl) (fun _ => rfl)))
    (fun x => (x.val.1,encodeNat x.val.2.val)) (fun _ => rfl) (fun _ => rfl)
def value (flip a z : Bool) (x : Input s b arity) := ResidualParentCoefficient.literal a z (prepared flip x)
noncomputable def computes (flip a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (treeLabelEncoding s b arity) (value flip a z) :=
  (prepareComputes flip s b arity).andThen (ResidualParentCoefficient.computes s b arity a z)
abbrev prepareMachine (flip : Bool) := (LeftMap.machine (ParentCoefficient.prepareMachine flip)).compose ResidualStoredWiring.machine
abbrev machine (flip a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :=
  (prepareMachine flip).compose (ResidualParentCoefficient.machine s b arity a z)
@[simp] theorem computes_machine (flip a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    (computes flip a z s b arity).machine=machine flip a z s b arity := rfl
theorem inFP (flip a z : Bool) : InFP (inputEncoding s b arity) (treeLabelEncoding s b arity) (value flip a z) :=
  (computes flip a z s b arity).inFP

/-- Exact original coefficient label for the literal conditioned assignment. -/
theorem value_conditioned (flip a z : Bool) (x : Input s b arity) :
    value flip a z x=
      (((x.val.1.val.1.1.val.labelNetwork x.val.1.val.1.1.property).asFinite).executableConditionEdge x.val.2 a z).vertex
        x.val.1.val.1.2 (ResidualParentCoefficient.survivingWord (prepared flip x)) :=
  ResidualParentCoefficient.literal_eq_conditioned a z (prepared flip x)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualStoredCoefficient
