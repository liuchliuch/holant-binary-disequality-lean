import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BranchDriver
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CycleQuery
import Holant.Complexity.GraphPreprocessing.ComponentSelection.Bounds

/-! Physically derived selective inputs for canonical original components.
The erased cycle invariant is proved from the executed surplus classifier; no
cut, root or classification certificate is extra encoded input. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentInputs
open Turing Computability BinaryCompose FixedFieldMachines ComponentSelection
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
abbrev Input := RawComponentCompiler.CanonicalInput

def preparedEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool where
  encode x := (pairEncoding ClassifyList.outputEncoding (RawComponentCompiler.canonicalEncoding s b arity)).encode (RawSurplus.value x.val,x)
  decode bits := do
    let (tag,x) ← (pairEncoding ClassifyList.outputEncoding (RawComponentCompiler.canonicalEncoding s b arity)).decode bits
    if tag=RawSurplus.value x.val then some x else none
  decode_encode x := by
    rw [(pairEncoding ClassifyList.outputEncoding (RawComponentCompiler.canonicalEncoding s b arity)).decode_encode]
    simp
noncomputable def classifyComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawComponentCompiler.canonicalEncoding s b arity) ClassifyList.outputEncoding (fun x => RawSurplus.value x.val) :=
  recode (RawSurplus.computes s b arity) Subtype.val (fun _ => rfl) (fun _ => rfl)
noncomputable def prepareComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawComponentCompiler.canonicalEncoding s b arity) (preparedEncoding s b arity) id :=
  recode (pairComputes (classifyComputes s b arity) (identityComputes (RawComponentCompiler.canonicalEncoding s b arity)))
    id (fun _ => rfl) (fun _ => rfl)
abbrev prepareMachine := pairMachine RawSurplus.machine identityMachine
@[simp] theorem prepare_machine (s b : ℕ) (arity : ℕ → ℕ) : (prepareComputes s b arity).machine=prepareMachine := rfl

def selectTree (x : Input s b arity) : Option (Input s b arity) := if RawSurplus.value x.val=.tree then some x else none
noncomputable def treeComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (preparedEncoding s b arity) (optionEncoding (RawComponentCompiler.canonicalEncoding s b arity)) selectTree :=
  recode (ComponentOption.computes false)
    (fun x => (RawSurplus.value x.val,(RawComponentCompiler.canonicalEncoding s b arity).encode x))
    (fun _ => rfl) (fun x => by
      cases h : RawSurplus.value x.val <;>
        simp [ComponentOption.value,selectTree,h,optionEncoding,Frame.wordEncoding])

def ValidCycle (x : ResidualContext.Query s b arity) : Prop :=
  RawComponentCompiler.Canonical (ResidualContext.original x) ∧
    RawSurplus.value (ResidualContext.original x)=.unicycle (ResidualContext.edge x.1).val
instance (x : ResidualContext.Query s b arity) : Decidable (ValidCycle x) := inferInstanceAs (Decidable (_∧_))
abbrev CycleInput (s b : ℕ) (arity : ℕ → ℕ) := {x : ResidualContext.Query s b arity // ValidCycle x}
def cycleEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (CycleInput s b arity) Bool where
  encode x := (CycleQuery.inputEncoding s b arity).encode x.val
  decode bits := do
    let x ← (CycleQuery.inputEncoding s b arity).decode bits
    if h : ValidCycle x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]
def residualEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (CycleInput s b arity) Bool where
  encode x := (ResidualContext.queryEncoding s b arity).encode x.val
  decode bits := do
    let x ← (ResidualContext.queryEncoding s b arity).decode bits
    if h : ValidCycle x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]

def mkCycle (x : Input s b arity) (e : ℕ) (h : RawSurplus.value x.val=.unicycle e) : CycleInput s b arity :=
  let context : ResidualContext.Input s b arity :=
    ⟨⟨x.val.1,⟨e,RawSurplus.unicycle_lt x.val e h⟩⟩,RawSurplus.unicycle_unused_id x.val e h⟩
  ⟨⟨context,x.val.2⟩,x.property,h⟩
def selectCycle (x : Input s b arity) : Option (CycleInput s b arity) :=
  match h : RawSurplus.value x.val with
  | .tree => none
  | .dense => none
  | .unicycle e => some (mkCycle x e h)
noncomputable def cycleComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (preparedEncoding s b arity) (optionEncoding (cycleEncoding s b arity)) selectCycle :=
  recode (ComponentOption.computes true)
    (fun x => (RawSurplus.value x.val,(RawComponentCompiler.canonicalEncoding s b arity).encode x))
    (fun _ => rfl) (fun x => by
      unfold selectCycle
      split <;>
        simp_all [ComponentOption.value,optionEncoding,Frame.wordEncoding,cycleEncoding,
          CycleQuery.inputEncoding,mkCycle,ResidualContext.original,pairEncoding,UnaryBinary.unaryEncoding,
          RawComponentCompiler.canonicalEncoding])
noncomputable def serializeComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (cycleEncoding s b arity) (residualEncoding s b arity) id :=
  recode (CycleQuery.computes s b arity) Subtype.val (fun _ => rfl) (fun _ => rfl)
@[simp] theorem tree_machine (s b : ℕ) (arity : ℕ → ℕ) : (treeComputes s b arity).machine=ComponentOption.machine false := rfl
@[simp] theorem cycle_machine (s b : ℕ) (arity : ℕ → ℕ) : (cycleComputes s b arity).machine=ComponentOption.machine true := rfl
@[simp] theorem serialize_machine (s b : ℕ) (arity : ℕ → ℕ) : (serializeComputes s b arity).machine=CycleQuery.machine := rfl

theorem prepared_length (x : Input s b arity) :
    ((preparedEncoding s b arity).encode x).length≤5*((RawClosedNetwork.encoding.encode x.val.1.val).length+2) := by
  have ht := RawSurplus.output_length x.val
  have hq := RawRootReach.input_length_le_original x.val
  change (Holant.Algebraic.frame (ClassifyList.outputEncoding.encode (RawSurplus.value x.val))++
    (RawRootReach.inputEncoding s b arity).encode x.val).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length]
  omega
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentInputs
