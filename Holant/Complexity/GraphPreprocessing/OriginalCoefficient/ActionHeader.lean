import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficientMeaning
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionAny
import Holant.Complexity.GraphPreprocessing.Traversal.OriginalTree
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.HeaderWords

/-! Original coefficient labels to the literal action-row header. The present
parent flag is read from the actual row. Direct frame parsing and bitwise literal emission preserve
label bytes; absent parents physically omit the unused b field. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeader
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev Labels (s b : ℕ) (arity : ℕ → ℕ) := RawClosedNetwork.TreeLabel s b arity
instance labelFintype (s b : ℕ) (arity : ℕ → ℕ) : Fintype (Labels s b arity) := by
  unfold Labels RawClosedNetwork.TreeLabel ExactSignatureTables.CoefficientIndex
  infer_instance
abbrev Data (s b : ℕ) (arity : ℕ → ℕ) := Bool × (Labels s b arity × Labels s b arity)
def dataEncoding (s b : ℕ) (arity : ℕ → ℕ) :=
  pairEncoding encodingBoolBool (pairEncoding (treeLabelEncoding s b arity) (treeLabelEncoding s b arity))
def emit (s b : ℕ) (arity : ℕ → ℕ) (x : Data s b arity) : List Bool :=
  Traversal.literals (Holant.Algebraic.frame ((treeLabelEncoding s b arity).encode x.2.1) ++
    if x.1 then Holant.Algebraic.frame ((treeLabelEncoding s b arity).encode x.2.2) else [])
def dataBound (s b : ℕ) (arity : ℕ → ℕ) := 3*lengthBound s b arity+4
theorem data_length (x : Data s b arity) : ((dataEncoding s b arity).encode x).length≤dataBound s b arity := by
  have ha := treeLabelEncoding_length_le s b arity x.2.1
  have hb := treeLabelEncoding_length_le s b arity x.2.2
  have hx : (encodingBoolBool.encode x.1).length=1 := by cases x.1 <;> rfl
  simp only [dataEncoding,pairEncoding_length,hx,dataBound]
  omega
noncomputable def emitComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (dataEncoding s b arity) Frame.wordEncoding (emit s b arity) :=
  recode (HeaderWords.computes.andThen LiteralBits.computes)
    (fun x => (x.1,((treeLabelEncoding s b arity).encode x.2.1,(treeLabelEncoding s b arity).encode x.2.2)))
    (fun _ => rfl) (fun _ => rfl)
abbrev emitMachine (_s _b : ℕ) (_arity : ℕ → ℕ) := HeaderWords.machine.compose LiteralBits.machine

noncomputable def presenceComputes : Computes ParentRowEncoding.row encodingBoolBool (fun row => row.parent.isSome) :=
  congrComputes (((recode (ed := optionEncoding ParentRowEncoding.endpoint) (g := Graph.ParentRow.parent)
    ParentEndpoint.computes id (fun _ => rfl) (fun row => by cases hp : row.parent <;> simp [hp,ParentRowEncoding.parent,optionEncoding])).andThen
    (OptionMap.computes (constantComputes ParentRowEncoding.endpoint encodingBoolBool true))).andThen OptionAny.computes)
    (fun row => by cases hp : row.parent <;> simp [Function.comp_def,hp,OptionAny.value])
abbrev presenceMachine : Machine :=
  (ParentEndpoint.machine.compose (OptionMap.machine (Constant.machine [true]))).compose OptionAny.machine
@[simp] theorem presence_machine : presenceComputes.machine=presenceMachine := rfl

def data (x : ParentCoefficient.Input s b arity) : Data s b arity :=
  (x.val.2.parent.isSome,(OrdinaryCoefficient.zeroValue x.val.1,ParentCoefficient.value false x))
noncomputable def zeroComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ParentCoefficient.inputEncoding s b arity) (treeLabelEncoding s b arity)
      (fun x => OrdinaryCoefficient.zeroValue x.val.1) :=
  recode ((Wiring.firstComputes (RawRootReach.inputEncoding s b arity) ParentRowEncoding.row).andThen
    (OrdinaryCoefficient.zeroComputes s b arity)) Subtype.val (fun _ => rfl) (fun _ => rfl)
noncomputable def flagComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ParentCoefficient.inputEncoding s b arity) encodingBoolBool (fun x => x.val.2.parent.isSome) :=
  recode ((Wiring.secondComputes (RawRootReach.inputEncoding s b arity) ParentRowEncoding.row).andThen presenceComputes)
    Subtype.val (fun _ => rfl) (fun _ => rfl)
noncomputable def dataComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ParentCoefficient.inputEncoding s b arity) (dataEncoding s b arity) data :=
  pairComputes (flagComputes s b arity) (pairComputes (zeroComputes s b arity) (ParentCoefficient.computes false s b arity))
def value (x : ParentCoefficient.Input s b arity) := emit s b arity (data x)
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ParentCoefficient.inputEncoding s b arity) Frame.wordEncoding value :=
  (dataComputes s b arity).andThen (emitComputes s b arity)
abbrev zeroMachine (s b : ℕ) (arity : ℕ → ℕ) := Wiring.firstMachine.compose (OrdinaryCoefficient.zeroMachine s b arity)
abbrev flagMachine := secondMachine.compose presenceMachine
abbrev dataMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  pairMachine flagMachine (pairMachine (zeroMachine s b arity) (ParentCoefficient.machine false s b arity))
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) := (dataMachine s b arity).compose (emitMachine s b arity)
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (ParentCoefficient.inputEncoding s b arity) Frame.wordEncoding value := (computes s b arity).inFP

theorem root_header (x : ParentCoefficient.Input s b arity) (hp : x.val.2.parent=none) :
    value x=Traversal.literals (Holant.Algebraic.frame ((treeLabelEncoding s b arity).encode (OrdinaryCoefficient.zeroValue x.val.1))) := by
  simp only [value,emit,data,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte,List.append_nil]
theorem child_header (x : ParentCoefficient.Input s b arity) (q : ℕ × Bool) (hp : x.val.2.parent=some q) :
    value x=Traversal.literals (Holant.Algebraic.frame ((treeLabelEncoding s b arity).encode (OrdinaryCoefficient.zeroValue x.val.1))++
      Holant.Algebraic.frame ((treeLabelEncoding s b arity).encode (ParentCoefficient.value false x))) := by
  simp only [value,emit,data,hp,Option.isSome_some,↓reduceIte]

noncomputable def originalComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding (fun x => value (ParentCoefficient.originalInput x)) :=
  (ParentCoefficient.originalPrepare s b arity).andThen (computes s b arity)
theorem original_inFP : InFP (RawRootReach.inputEncoding s b arity) Frame.wordEncoding
    (fun x => value (ParentCoefficient.originalInput x)) := (originalComputes s b arity).inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeader
