import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentCompiler
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParentCoefficientSpec

/-! A retained original graph and one original nonparent cut edge. The unused
condition is a semantic invariant established by surplus selection, never an
extra tape field or a supplied size certificate. Every encoded ID is original. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualContext
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev Data (s b : ℕ) (arity : ℕ → ℕ) := Σ r : {r : RawClosedNetwork // r.WellFormed s b arity}, Fin r.val.edges.length
def Unused (x : Data s b arity) : Prop :=
  ∀ v : Fin x.1.val.vertices.length, ∀ q∈((x.1.val.graph x.1.property).parentRow v).parent, q.1≠x.2.val
instance (x : Data s b arity) : Decidable (Unused x) := inferInstanceAs (Decidable (∀ v : Fin x.1.val.vertices.length, ∀ q∈_, _))
abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := {x : Data s b arity // Unused x}
def dataEncoding (s b : ℕ) (arity : ℕ → ℕ) :=
  sigmaEncoding (RawClosedNetwork.validatedEncoding s b arity) (fun r => SignatureLabel.binaryFinEncoding r.val.edges.length)
def encoding (s b : ℕ) (arity : ℕ → ℕ) : Encoding (Input s b arity) Bool where
  encode x := (dataEncoding s b arity).encode x.val
  decode bits := do
    let x ← (dataEncoding s b arity).decode bits
    if h : Unused x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]
abbrev source (x : Input s b arity) := x.val.1
abbrev edge (x : Input s b arity) := x.val.2
abbrev Query (s b : ℕ) (arity : ℕ → ℕ) := Σ x : Input s b arity, Fin (source x).val.vertices.length
def queryEncoding (s b : ℕ) (arity : ℕ → ℕ) :=
  sigmaEncoding (encoding s b arity) (fun x => OccurrenceLabel.unaryPortEncoding (source x).val.vertices.length)
def original (x : Query s b arity) : RawRootReach.Input s b arity := ⟨source x.1,x.2⟩

theorem vertex_bound (x : Input s b arity) : (source x).val.vertices.length≤((encoding s b arity).encode x).length := by
  have h := (source x).val.counts_le_encoded_length
  change (source x).val.vertices.length≤(Holant.Algebraic.frame (RawClosedNetwork.encoding.encode (source x).val)++encodeNat (edge x).val).length
  simp only [List.length_append,Holant.Algebraic.frame_length]
  omega
theorem encoded_length (x : Input s b arity) :
    ((encoding s b arity).encode x).length≤3*((RawClosedNetwork.encoding.encode (source x).val).length+1) := by
  have hq := NetworkLookup.query_bits_le (source x).val (source x).property ((source x).val.lookup (source x).property (edge x,false))
  have he : (source x).val.portEndpoint (source x).property ((source x).val.lookup (source x).property (edge x,false))=((edge x).val,false) :=
    congrArg (fun p : Fin (source x).val.edges.length × Bool => (p.1.val,p.2)) ((source x).val.route_lookup (source x).property (edge x,false))
  rw [he] at hq
  simp only [RawClosedNetwork.endpointEncoding,framedProductEncoding_length,encodingNatBool,encodingBoolBool,encodeBool,List.length_singleton] at hq
  change (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode (source x).val)++encodeNat (edge x).val).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length]
  omega
theorem query_length (x : Query s b arity) :
    ((queryEncoding s b arity).encode x).length≤7*((RawClosedNetwork.encoding.encode (source x.1).val).length+1) := by
  have he := encoded_length x.1
  have hv := x.2.isLt
  have hc := (source x.1).val.counts_le_encoded_length
  change (Holant.Algebraic.frame ((encoding s b arity).encode x.1)++List.replicate x.2.val true).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

/-- Actual word projections recover the original raw/vertex query. -/
noncomputable def originalComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (queryEncoding s b arity) (RawRootReach.inputEncoding s b arity) original :=
  recode ActionChild.queryWire (fun x => ((RawClosedNetwork.encoding.encode (source x.1).val,encodeNat (edge x.1).val),List.replicate x.2.val true))
    (fun _ => rfl) (fun _ => rfl)
abbrev originalMachine := ActionChild.queryMachine
@[simp] theorem original_machine (s b : ℕ) (arity : ℕ → ℕ) : (originalComputes s b arity).machine=originalMachine := rfl

noncomputable def edgeComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (queryEncoding s b arity) Frame.wordEncoding (fun x => encodeNat (edge x.1).val) :=
  recode ((Wiring.firstComputes ActionChild.words Frame.wordEncoding).andThen
    (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding))
    (fun x => ((RawClosedNetwork.encoding.encode (source x.1).val,encodeNat (edge x.1).val),List.replicate x.2.val true))
    (fun _ => rfl) (fun _ => rfl)
abbrev edgeMachine := Wiring.firstMachine.compose secondMachine
@[simp] theorem edge_machine (s b : ℕ) (arity : ℕ → ℕ) : (edgeComputes s b arity).machine=edgeMachine := rfl
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualContext
