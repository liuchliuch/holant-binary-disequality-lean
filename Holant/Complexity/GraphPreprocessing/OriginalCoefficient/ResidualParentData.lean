import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOptionalSurvivorInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonData

/-! One original query for both root and nonroot conditioned coefficients. The
surviving endpoint is optional and must, when present, differ from the cut edge.
Original raw graph, target, cut ID and stored parent orientation remain literal. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParent
open Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Data (s b : ℕ) (arity : ℕ → ℕ) :=
  Σ r : {r : RawClosedNetwork // r.WellFormed s b arity},
    Fin r.val.vertices.length × (Fin r.val.edges.length × Option (Fin r.val.edges.length × Bool))

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) :=
  {x : Data s b arity // ∀ q ∈ x.2.2.2, x.2.2.1 ≠ q.1}

def dataEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Data s b arity) Bool :=
  sigmaEncoding (RawClosedNetwork.validatedEncoding s b arity) (fun r =>
    pairEncoding (OccurrenceLabel.unaryPortEncoding r.val.vertices.length)
      (pairEncoding (SignatureLabel.binaryFinEncoding r.val.edges.length)
        (optionEncoding (pairEncoding (SignatureLabel.binaryFinEncoding r.val.edges.length) ParentRowEncoding.orientation))))

def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool where
  encode x := (dataEncoding s b arity).encode x.val
  decode bits := do
    let x ← (dataEncoding s b arity).decode bits
    if h : ∀ q ∈ x.2.2.2, x.2.2.1 ≠ q.1 then some ⟨x,h⟩ else none
  decode_encode x := by
    rw [Encoding.decode_encode]
    change (if h : ∀ q ∈ x.val.2.2.2, x.val.2.2.1 ≠ q.1 then some ⟨x.val,h⟩ else none) = some x
    rw [dif_pos x.property]

variable {s b : ℕ} {arity : ℕ → ℕ}

def cutQuery (x : Input s b arity) : ResidualPinQuery.Input s b arity :=
  ⟨x.val.1,x.val.2.1,x.val.2.2.1⟩

def survivorQuery (x : Input s b arity) : ResidualOptionalSurvivor.Input s b arity :=
  ⟨x.val.1,x.val.2.1,x.val.2.2.2⟩

def parentBits (x : Input s b arity) : List Bool :=
  (optionEncoding (pairEncoding (SignatureLabel.binaryFinEncoding x.val.1.val.edges.length)
    ParentRowEncoding.orientation)).encode x.val.2.2.2

def words (x : Input s b arity) : List Bool × (List Bool × (List Bool × List Bool)) :=
  (RawClosedNetwork.encoding.encode x.val.1.val,List.replicate x.val.2.1.val true,
    encodeNat x.val.2.2.1.val,parentBits x)

noncomputable def cutComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ResidualPinQuery.inputEncoding s b arity) cutQuery :=
  recode (rightMapComputes Frame.wordEncoding (rightMapComputes Frame.wordEncoding
    (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding))) words (fun _ => rfl) (fun _ => rfl)

noncomputable def survivorComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ResidualOptionalSurvivor.inputEncoding s b arity) survivorQuery :=
  recode (rightMapComputes Frame.wordEncoding (rightMapComputes Frame.wordEncoding
    (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding))) words (fun _ => rfl) (fun _ => rfl)

abbrev cutMachine := ResidualSingleton.cutMachine
abbrev survivorMachine := ResidualSingleton.survivorMachine

@[simp] theorem cutComputes_machine (s b : ℕ) (arity : ℕ → ℕ) : (cutComputes s b arity).machine = cutMachine := rfl
@[simp] theorem survivorComputes_machine (s b : ℕ) (arity : ℕ → ℕ) : (survivorComputes s b arity).machine = survivorMachine := rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParent
