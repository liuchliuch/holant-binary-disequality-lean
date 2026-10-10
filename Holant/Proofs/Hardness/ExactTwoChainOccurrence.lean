import Holant.Proofs.Hardness.ExactTwoChainLocalRows
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.RawCorrectness

/-! Actual all-occurrence four-port chain compiler. Original row parsing,
ordinal traversal and framing are reused; each marked occurrence gets k+1
q vertices and2k fresh native edges. Every unmarked original row is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainOccurrence
open Turing Computability Holant Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution RawClosedNetwork
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
export Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
  (Input inputEncoding Query queryEncoding contextComputes indexComputes lengthComputes sourceComputes
   originalQuery originalQueryComputes originalRowComputes before beforeComputes multiplyComputes
   marked markedComputes allRowsComputes repeatEdgesComputes identity_place)
namespace Local
export ExactTwoChainLocalRows (LocalInput localEncoding placedRows rowsComputes placedRows_eq)
end Local
export ExactTwoChainRecords (explicitTemplate)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

def binaryDouble : Computes encodingNatBool encodingNatBool (fun n : ℕ=>2*n) :=
  congrComputes ((pairComputes (identityComputes encodingNatBool) (identityComputes encodingNatBool)).andThen
    FixedGadgetSubstitution.Compiler.addComputes) (fun n=>by change n+n=2*n; omega)

def unaryDouble : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun n : ℕ=>2*n) :=
  recode (FixedGadgetSubstitution.Compiler.joinComputes (FixedGadgetSubstitution.Compiler.encodeComputes UnaryBinary.unaryEncoding)
    (FixedGadgetSubstitution.Compiler.encodeComputes UnaryBinary.unaryEncoding)) id (fun _=>rfl)
    (fun n=>by
      change List.replicate n true ++ List.replicate n true=List.replicate (2*n) true
      rw [←List.replicate_add,Nat.two_mul])

variable (s b : ℕ) (arity : ℕ → ℕ)

def offset (distinguished : ℕ) (x : Query s b arity) : ℕ :=
  x.1.2.val.edges.length + 2*x.1.1 * before s b arity distinguished x

noncomputable def offsetComputes (distinguished : ℕ) : Computes (queryEncoding s b arity)
    encodingNatBool (offset s b arity distinguished) :=
  (pairComputes
    (((sourceComputes s b arity).andThen
      (FixedGadgetSubstitution.Compiler.edgeCountComputes s b arity)).andThen UnaryBinary.computes)
    ((pairComputes (((lengthComputes s b arity).andThen UnaryBinary.computes).andThen binaryDouble)
      ((beforeComputes s b arity distinguished).andThen UnaryBinary.computes)).andThen multiplyComputes)).andThen
        FixedGadgetSubstitution.Compiler.addComputes

def placement (distinguished : ℕ) (x : Query s b arity) : Local.LocalInput :=
  (x.1.1,(offset s b arity distinguished x,(x.1.2.val.vertices.get x.2).2))

noncomputable def placementComputes (distinguished : ℕ) : Computes (queryEncoding s b arity)
    Local.localEncoding (placement s b arity distinguished) :=
  pairComputes (lengthComputes s b arity)
    (pairComputes (offsetComputes s b arity distinguished)
      ((originalRowComputes s b arity).andThen
        (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
          id (fun _ => rfl) (fun _ => rfl))))
def rows (distinguished label : ℕ) (x : Query s b arity) : List RawVertex :=
  if marked s b arity distinguished x then
    Local.placedRows label (placement s b arity distinguished x) else [x.1.2.val.vertices.get x.2]

noncomputable def rowChunkComputes (distinguished label : ℕ) : Computes (queryEncoding s b arity)
    Frame.wordEncoding (fun x => FixedGadgetSubstitution.Compiler.entries vertexEncoding
      (rows s b arity distinguished label x)) := by
  let yes := ((placementComputes s b arity distinguished).andThen
    (Local.rowsComputes label)).andThen (FixedGadgetSubstitution.Compiler.entriesComputes vertexEncoding)
  let no := (originalRowComputes s b arity).andThen (FixedGadgetSubstitution.Compiler.entryComputes vertexEncoding)
  refine congrComputes (ifComputes (markedComputes s b arity distinguished) yes no) ?_
  intro x
  cases h : marked s b arity distinguished x <;>
    simp [rows,h,FixedGadgetSubstitution.Compiler.entries]

def edgeRows (distinguished edge : ℕ) (x : Query s b arity) : List ℕ :=
  if marked s b arity distinguished x then List.replicate (2*x.1.1) edge else []

noncomputable def edgeChunkComputes (distinguished edge : ℕ) :
    Computes (queryEncoding s b arity) Frame.wordEncoding
      (fun x => FixedGadgetSubstitution.Compiler.entries encodingNatBool
        (edgeRows s b arity distinguished edge x)) := by
  let yes := (((lengthComputes s b arity).andThen unaryDouble).andThen (repeatEdgesComputes edge)).andThen
    (FixedGadgetSubstitution.Compiler.entriesComputes encodingNatBool)
  let no := constantComputes (queryEncoding s b arity) Frame.wordEncoding []
  refine congrComputes (ifComputes (markedComputes s b arity distinguished) yes no) ?_
  intro x
  cases h : marked s b arity distinguished x <;>
    simp [edgeRows,h,FixedGadgetSubstitution.Compiler.entries]

def vertices (distinguished label : ℕ) (x : Input s b arity) : List RawVertex :=
  (List.finRange x.2.val.vertices.length).flatMap
    (fun i => rows s b arity distinguished label ⟨x,i⟩)

def edges (distinguished edge : ℕ) (x : Input s b arity) : List ℕ :=
  x.2.val.edges ++ (List.finRange x.2.val.vertices.length).flatMap
    (fun i => edgeRows s b arity distinguished edge ⟨x,i⟩)

noncomputable def verticesComputes (distinguished label : ℕ) : Computes (inputEncoding s b arity)
    (framedListEncoding vertexEncoding) (vertices s b arity distinguished label) := by
  let run := allRowsComputes s b arity _ (rowChunkComputes s b arity distinguished label)
  refine recode (FixedGadgetSubstitution.Compiler.joinComputes run
    (constantComputes (inputEncoding s b arity) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro x
  have h := FixedGadgetSubstitution.Compiler.entries_append_encode vertexEncoding
    (vertices s b arity distinguished label x) []
  simpa only [vertices,FixedGadgetSubstitution.Compiler.entries,List.flatMap_assoc,
    List.append_nil,framedListEncode,framedListEncoding,Frame.wordEncoding,id_eq,Function.comp_def] using h

noncomputable def edgesComputes (distinguished edge : ℕ) : Computes (inputEncoding s b arity)
    (framedListEncoding encodingNatBool) (edges s b arity distinguished edge) := by
  let original := (((Wiring.secondComputes UnaryBinary.unaryEncoding (validatedEncoding s b arity)).andThen
    (FixedGadgetSubstitution.Compiler.edgesComputes s b arity)).andThen
      (FixedGadgetSubstitution.Compiler.entriesComputes encodingNatBool))
  let added := allRowsComputes s b arity _ (edgeChunkComputes s b arity distinguished edge)
  refine recode (FixedGadgetSubstitution.Compiler.joinComputes
    (FixedGadgetSubstitution.Compiler.joinComputes original added)
    (constantComputes (inputEncoding s b arity) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro x
  have h := FixedGadgetSubstitution.Compiler.entries_append_encode encodingNatBool
    (edges s b arity distinguished edge x) []
  simpa only [edges,FixedGadgetSubstitution.Compiler.entries,List.flatMap_assoc,List.flatMap_append,
    List.append_nil,framedListEncode,framedListEncoding,Frame.wordEncoding,id_eq,Function.comp_def] using h

def raw (distinguished label edge : ℕ) (x : Input s b arity) : RawClosedNetwork :=
  ⟨vertices s b arity distinguished label x, edges s b arity distinguished edge x⟩

/-- One fixed finite program accepts the original graph and a variable unary k.
Its actual primitive Boolean cost is polynomial in those original input bytes. -/
noncomputable def rawComputes (distinguished label edge : ℕ) :
    Computes (inputEncoding s b arity) encoding (raw s b arity distinguished label edge) :=
  recode (pairComputes (verticesComputes s b arity distinguished label)
    (edgesComputes s b arity distinguished edge)) id (fun _ => rfl) (fun _ => rfl)

theorem raw_inFP (distinguished label edge : ℕ) :
    InFP (inputEncoding s b arity) encoding (raw s b arity distinguished label edge) :=
  (rawComputes s b arity distinguished label edge).inFP

theorem primitive_bound (distinguished label edge : ℕ) (x : Input s b arity) :
    primitiveCost (rawComputes s b arity distinguished label edge).machine
      ((rawComputes s b arity distinguished label edge).outputs x).steps
      (some (initList (rawComputes s b arity distinguished label edge).machine.computer
        ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial (rawComputes s b arity distinguished label edge)).eval
        ((inputEncoding s b arity).encode x).length :=
  computes_primitive_cost (rawComputes s b arity distinguished label edge) x

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainOccurrence
