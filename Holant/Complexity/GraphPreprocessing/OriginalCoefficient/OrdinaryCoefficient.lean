import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexDescriptorInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivorInterface
import Holant.Complexity.FixedFieldMachines.LeftMap

/-! Clean ordinary coefficient producers. A fixed absent-pin pref is physically
loaded; optional singleton ports come from the actual original-incidence lookup.
No deleted edge, semantic coefficient value, or unproved certificate is input. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev prefixMachine (pref : List Bool) : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Option Bool × Unit
  initial := (none,())
  program _ := Constant.pushWord () pref .halt

theorem prefix_exact (pref word : List Bool) :
    RunsExactly (prefixMachine pref).computer.step
      (initList (prefixMachine pref).computer word)
      (haltList (prefixMachine pref).computer (pref++word)) 1 := by
  apply runsExactly_one
  rw [Machine.init_eq,Machine.halt_eq]
  change some (TM2.stepAux (Constant.pushWord () pref .halt) (none,()) (wordTape () word))=_
  rw [Constant.pushWord_eval]
  rfl

noncomputable def prefixComputes (pref : List Bool) :
    Computes Frame.wordEncoding Frame.wordEncoding (fun word => pref++word) where
  machine := prefixMachine pref
  time := 1
  outputs word := {steps := 1, evals_in_steps := prefix_exact pref word, steps_le_m := by simp}

def noPins {n : ℕ} (port : Option (Fin n)) : ResidualLabel.Descriptor n :=
  ⟨(none,none,port),by simp [ResidualLabel.Valid]⟩

def absentPins : List Bool := [true,false,false,true,false,false]
theorem noPins_encode {n : ℕ} (port : Option (Fin n)) :
    (ResidualLabel.descriptorEncoding n).encode (noPins port) =
      absentPins++(optionEncoding (OccurrenceLabel.unaryPortEncoding n)).encode port := rfl

variable {s b : ℕ} {arity : ℕ → ℕ}

def zeroEntry (x : RawRootReach.Input s b arity) : VertexDescriptor.Input s b arity := ⟨x,noPins none⟩
def zeroValue (x : RawRootReach.Input s b arity) : RawClosedNetwork.TreeLabel s b arity :=
  some (.inl ⟨x.1.val.signatureLabel x.1.property x.2,fun _ => false⟩)

noncomputable def zeroPrepare (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) (VertexDescriptor.inputEncoding s b arity) zeroEntry :=
  recode (pairComputes (identityComputes (RawRootReach.inputEncoding s b arity))
    (constantComputes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding (absentPins++[false])))
    id (fun _ => rfl) (fun _ => rfl)

theorem zero_literal (x : RawRootReach.Input s b arity) :
    VertexDescriptor.literal s b arity (zeroEntry x)=zeroValue x := by
  simp [VertexDescriptor.literal,zeroEntry,zeroValue,ResidualVertex.label,ResidualLabel.literal,
    ResidualLabel.assignment,ResidualLabel.pinAt,noPins]
  funext j
  rfl

noncomputable def zeroComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) (treeLabelEncoding s b arity) zeroValue :=
  congrComputes ((zeroPrepare s b arity).andThen (VertexDescriptor.computes s b arity)) zero_literal

abbrev zeroMachine (s b : ℕ) (arity : ℕ → ℕ) : Machine :=
  (pairMachine identityMachine (Constant.machine (absentPins++[false]))).compose (VertexDescriptor.machine s b arity)
@[simp] theorem zero_machine (s b : ℕ) (arity : ℕ → ℕ) : (zeroComputes s b arity).machine=zeroMachine s b arity := rfl

abbrev Input := ResidualOptionalSurvivor.Input
abbrev inputEncoding := ResidualOptionalSurvivor.inputEncoding
def context (x : Input s b arity) : RawRootReach.Input s b arity := ⟨x.1,x.2.1⟩
def descriptor (x : Input s b arity) := noPins (ResidualOptionalSurvivor.selected x)
def entry (x : Input s b arity) : VertexDescriptor.Input s b arity := ⟨context x,descriptor x⟩
def value (x : Input s b arity) : RawClosedNetwork.TreeLabel s b arity :=
  some (.inl ⟨x.1.val.signatureLabel x.1.property x.2.1,
    fun j => decide (ResidualOptionalSurvivor.selected x=some j)⟩)

def words := pairEncoding Frame.wordEncoding Frame.wordEncoding
def wireEncoding := pairEncoding Frame.wordEncoding words
noncomputable def contextWire : Computes wireEncoding words (fun x => (x.1,x.2.1)) :=
  pairComputes (Wiring.firstComputes Frame.wordEncoding words)
    ((Wiring.secondComputes Frame.wordEncoding words).andThen
      (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding))

def wireInput (x : Input s b arity) : List Bool × (List Bool × List Bool) :=
  (RawClosedNetwork.encoding.encode x.1.val,(List.replicate x.2.1.val true,
    (optionEncoding (pairEncoding (SignatureLabel.binaryFinEncoding x.1.val.edges.length)
      ParentRowEncoding.orientation)).encode x.2.2))

noncomputable def contextComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (RawRootReach.inputEncoding s b arity) context :=
  recode contextWire wireInput (fun _ => rfl) (fun _ => rfl)

noncomputable def descriptorComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) Frame.wordEncoding
      (fun x => absentPins++ResidualOptionalSurvivor.portBits x) :=
  (ResidualOptionalSurvivor.computes s b arity).andThen (prefixComputes absentPins)

noncomputable def prepareComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (VertexDescriptor.inputEncoding s b arity) entry :=
  recode (pairComputes (contextComputes s b arity) (descriptorComputes s b arity)) id
    (fun _ => rfl) (fun x => by
      change Holant.Algebraic.frame _++(absentPins++ResidualOptionalSurvivor.portBits x)=
        Holant.Algebraic.frame _++(ResidualLabel.descriptorEncoding _).encode (descriptor x)
      rw [descriptor,noPins_encode,ResidualOptionalSurvivor.selected_encode]
      rfl)

theorem literal_eq (x : Input s b arity) : VertexDescriptor.literal s b arity (entry x)=value x := by
  simp [VertexDescriptor.literal,entry,context,descriptor,value,ResidualVertex.label,
    ResidualLabel.literal,ResidualLabel.assignment,ResidualLabel.pinAt,noPins]
  funext j
  rfl

noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (treeLabelEncoding s b arity) value :=
  congrComputes ((prepareComputes s b arity).andThen (VertexDescriptor.computes s b arity)) literal_eq

abbrev contextMachine : Machine := pairMachine Wiring.firstMachine (secondMachine.compose Wiring.firstMachine)
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) : Machine :=
  (pairMachine contextMachine (ResidualOptionalSurvivor.machine.compose (prefixMachine absentPins))).compose
    (VertexDescriptor.machine s b arity)
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl

theorem zero_inFP : InFP (RawRootReach.inputEncoding s b arity) (treeLabelEncoding s b arity) zeroValue :=
  (zeroComputes s b arity).inFP
theorem inFP : InFP (inputEncoding s b arity) (treeLabelEncoding s b arity) value :=
  (computes s b arity).inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient
