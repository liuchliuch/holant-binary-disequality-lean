import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSurvivorInterface
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! The one original query needed for all three residual descriptor fields.
The surviving endpoint belongs to a different edge from the removed edge.
The word contains raw graph, original target, cut ID and surviving endpoint;
all coordinate bounds and collision guarantees come from these original IDs. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
open Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Data (s b : ℕ) (arity : ℕ → ℕ) :=
  Σ r : {r : RawClosedNetwork // r.WellFormed s b arity},
    Fin r.val.vertices.length × (Fin r.val.edges.length × (Fin r.val.edges.length × Bool))

abbrev Input (s b : ℕ) (arity : ℕ → ℕ) :=
  {x : Data s b arity // x.2.2.1 ≠ x.2.2.2.1}

def dataEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Data s b arity) Bool :=
  sigmaEncoding (RawClosedNetwork.validatedEncoding s b arity) (fun r =>
    pairEncoding (OccurrenceLabel.unaryPortEncoding r.val.vertices.length)
      (pairEncoding (SignatureLabel.binaryFinEncoding r.val.edges.length)
        (pairEncoding (SignatureLabel.binaryFinEncoding r.val.edges.length) ParentRowEncoding.orientation)))

def inputEncoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool where
  encode x := (dataEncoding s b arity).encode x.val
  decode bits := do
    let x ← (dataEncoding s b arity).decode bits
    if h : x.2.2.1 ≠ x.2.2.2.1 then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]

variable {s b : ℕ} {arity : ℕ → ℕ}

def cutQuery (x : Input s b arity) : ResidualPinQuery.Input s b arity :=
  ⟨x.val.1,x.val.2.1,x.val.2.2.1⟩

def survivorQuery (x : Input s b arity) : ResidualSurvivorQuery.Input s b arity :=
  ⟨x.val.1,x.val.2.1,x.val.2.2.2⟩

def words (x : Input s b arity) : List Bool × (List Bool × (List Bool × List Bool)) :=
  (RawClosedNetwork.encoding.encode x.val.1.val,
    List.replicate x.val.2.1.val true, encodeNat x.val.2.2.1.val,
    RawClosedNetwork.endpointEncoding.encode (x.val.2.2.2.1.val,x.val.2.2.2.2))

/-- Two real right-map combinators remove only the survivor query. -/
noncomputable def cutComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ResidualPinQuery.inputEncoding s b arity) cutQuery :=
  recode (rightMapComputes Frame.wordEncoding (rightMapComputes Frame.wordEncoding
    (Wiring.firstComputes Frame.wordEncoding Frame.wordEncoding))) words
    (fun _ => rfl) (fun _ => rfl)

/-- Two real right-map combinators remove only the cut-edge ID. The original
endpoint orientation travels unchanged into the dynamic endpoint lookup. -/
noncomputable def survivorComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (inputEncoding s b arity) (ResidualSurvivorQuery.inputEncoding s b arity) survivorQuery :=
  recode (rightMapComputes Frame.wordEncoding (rightMapComputes Frame.wordEncoding
    (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding))) words
    (fun _ => rfl) (fun _ => rfl)

abbrev cutMachine : Machine := rightMapMachine (rightMapMachine Wiring.firstMachine)
abbrev survivorMachine : Machine := rightMapMachine (rightMapMachine secondMachine)

@[simp] theorem cutComputes_machine (s b : ℕ) (arity : ℕ → ℕ) :
    (cutComputes s b arity).machine = cutMachine := rfl
@[simp] theorem survivorComputes_machine (s b : ℕ) (arity : ℕ → ℕ) :
    (survivorComputes s b arity).machine = survivorMachine := rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
