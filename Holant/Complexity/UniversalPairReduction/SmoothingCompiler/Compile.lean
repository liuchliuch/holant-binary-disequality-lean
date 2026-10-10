import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Marked
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Endpoints
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! Literal finite-machine compilation of native-X smoothing. The program scans
original labels, extracts the two ordered ports, deletes the marked row, remaps
every remaining endpoint, and physically emits the residual X-edge records. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev Context := RawEndpoint × RawEndpoint
abbrev contextEncoding := pairEncoding endpointEncoding endpointEncoding

def remap (c : Context) (p : RawEndpoint) : RawEndpoint :=
  if c.1.1=c.2.1 then Smoothing.removeLoopEndpoint c.1.1 p
  else Smoothing.spliceEndpoint c.1 c.2 p

def circle (c : Context) : Bool := decide (c.1.1=c.2.1)
noncomputable def circleComputes : Computes contextEncoding encodingBoolBool circle :=
  (pairComputes
    ((Wiring.firstComputes endpointEncoding endpointEncoding).andThen Endpoints.edgeComputes)
    ((Wiring.secondComputes endpointEncoding endpointEncoding).andThen Endpoints.edgeComputes)).andThen
      Endpoints.equalComputes

noncomputable def remapComputes : Computes (pairEncoding contextEncoding endpointEncoding)
    endpointEncoding (fun x => remap x.1 x.2) := by
  let ctx := Wiring.firstComputes contextEncoding endpointEncoding
  let cur := Wiring.secondComputes contextEncoding endpointEncoding
  let first := ctx.andThen (Wiring.firstComputes endpointEncoding endpointEncoding)
  let second := ctx.andThen (Wiring.secondComputes endpointEncoding endpointEncoding)
  let loop := (pairComputes (first.andThen Endpoints.edgeComputes) cur).andThen
    Endpoints.removeLoopEndpointComputes
  let splice := (pairComputes first (pairComputes second cur)).andThen Endpoints.spliceEndpointComputes
  exact congrComputes (ifComputes (ctx.andThen circleComputes) loop splice)
    (fun x => by simp [circle,remap])

def remapRow (c : Context) (row : RawVertex) : RawVertex := (row.1,row.2.map (remap c))
noncomputable def remapRowComputes : Computes (pairEncoding contextEncoding vertexEncoding)
    vertexEncoding (fun x => remapRow x.1 x.2) := by
  let ctx := Wiring.firstComputes contextEncoding vertexEncoding
  let row := Wiring.secondComputes contextEncoding vertexEncoding
  let label := row.andThen (recode
    (Wiring.firstComputes encodingNatBool (framedListEncoding endpointEncoding))
      id (fun _ => rfl) (fun _ => rfl))
  let ends := row.andThen (recode
    (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
      id (fun _ => rfl) (fun _ => rfl))
  exact recode (pairComputes label ((pairComputes ctx ends).andThen
    (mapListComputes contextEncoding endpointEncoding endpointEncoding remap remapComputes)))
      id (fun _ => rfl) (fun _ => rfl)

variable (s : ℕ) (arity : ℕ → ℕ)
def rowChunk (x : Context × RawVertex) : List Bool :=
  if x.2.1 == s then [] else FixedGadgetSubstitution.Compiler.entry vertexEncoding (remapRow x.1 x.2)
noncomputable def rowChunkComputes : Computes (pairEncoding contextEncoding vertexEncoding)
    Frame.wordEncoding (rowChunk s) := by
  let row := Wiring.secondComputes contextEncoding vertexEncoding
  let label := row.andThen (recode
    (Wiring.firstComputes encodingNatBool (framedListEncoding endpointEncoding))
      id (fun _ => rfl) (fun _ => rfl))
  let test := (pairComputes label
    (constantComputes (pairEncoding contextEncoding vertexEncoding) encodingNatBool s)).andThen
      Endpoints.equalComputes
  exact congrComputes (ifComputes test
    (constantComputes (pairEncoding contextEncoding vertexEncoding) Frame.wordEncoding [])
    (remapRowComputes.andThen (FixedGadgetSubstitution.Compiler.entryComputes vertexEncoding))) (fun x => by
      simp [rowChunk,beq_iff_eq])

def remainingRows (c : Context) (rows : List RawVertex) : List RawVertex :=
  (rows.filter (fun row => row.1 != s)).map (remapRow c)

theorem row_chunks (c : Context) (rows : List RawVertex) :
    rows.flatMap (fun row => rowChunk s (c,row)) =
      FixedGadgetSubstitution.Compiler.entries vertexEncoding (remainingRows s c rows) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [List.flatMap_cons,ih]
    by_cases h : row.1=s <;> simp [rowChunk,remainingRows,h,FixedGadgetSubstitution.Compiler.entries]

noncomputable def remainingRowsComputes : Computes
    (pairEncoding contextEncoding (framedListEncoding vertexEncoding))
    (framedListEncoding vertexEncoding) (fun x => remainingRows s x.1 x.2) := by
  let provider : Computes (sigmaEncoding contextEncoding (fun _ => vertexEncoding)) Frame.wordEncoding
      (fun x => rowChunk s (x.1,x.2)) :=
    recode (rowChunkComputes s) (fun x => (x.1,x.2)) (fun _ => rfl) (fun _ => rfl)
  let run := ContextFlatMap.computes contextEncoding (fun _ => vertexEncoding) _ provider
  let run' : Computes (pairEncoding contextEncoding (framedListEncoding vertexEncoding))
      Frame.wordEncoding (fun x => FixedGadgetSubstitution.Compiler.entries vertexEncoding (remainingRows s x.1 x.2)) :=
    recode run (fun x => ⟨x.1,x.2⟩) (fun _ => rfl) (fun x => row_chunks s x.1 x.2)
  refine recode (FixedGadgetSubstitution.Compiler.joinComputes run'
    (constantComputes _ Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro x
  simpa only [List.append_nil,framedListEncode,framedListEncoding,Frame.wordEncoding,id_eq] using
    FixedGadgetSubstitution.Compiler.entries_append_encode vertexEncoding (remainingRows s x.1 x.2) []

noncomputable def zerosComputes : Computes UnaryBinary.unaryEncoding
    (framedListEncoding encodingNatBool) (fun n => List.replicate n 0) := by
  let e := pairEncoding Frame.wordEncoding UnaryBinary.unaryEncoding
  let w : Computes e encodingNatBool (fun _ => 0) := constantComputes e encodingNatBool 0
  let prepare := pairComputes
    (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding []) ComponentSelection.UnaryRange.computes
  exact congrComputes (prepare.andThen (mapListComputes Frame.wordEncoding UnaryBinary.unaryEncoding
    encodingNatBool (fun _ _ => 0) w)) (fun n => by simp)

def context (r : RawClosedNetwork) : Context :=
  ((markedEnds s r).getD 0 (0,false),(markedEnds s r).getD 1 (0,false))
noncomputable def contextComputes : Computes (inputEncoding s arity) contextEncoding
    (fun r => context s r.val) := pairComputes (firstComputes s arity) (secondComputes s arity)

def residual (r : RawClosedNetwork) : RawClosedNetwork where
  vertices := remainingRows s (context s r) r.vertices
  edges := List.replicate (r.edges.length-1) 0

noncomputable def residualComputes : Computes (inputEncoding s arity) encoding
    (fun r => residual s r.val) := by
  let source := forgetComputes s arity
  let rows := (pairComputes (contextComputes s arity)
    (source.andThen (FixedGadgetSubstitution.Compiler.rowsComputes (s+1) 1 (extendedArity s arity)))).andThen
      (remainingRowsComputes s)
  let edges := ((source.andThen (FixedGadgetSubstitution.Compiler.edgeCountComputes (s+1) 1 (extendedArity s arity))).andThen
    Endpoints.unaryPredecessorComputes).andThen zerosComputes
  exact recode (pairComputes rows edges) id (fun _ => rfl) (fun _ => rfl)

abbrev resultEncoding := pairEncoding encoding encodingBoolBool

def value (r : RawClosedNetwork) : RawClosedNetwork × Bool :=
  if present s r then (residual s r,circle (context s r)) else (r,false)

noncomputable def valueComputes : Computes (inputEncoding s arity) resultEncoding
    (fun r => value s r.val) :=
  ifComputes (presentComputes s arity)
    (pairComputes (residualComputes s arity) ((contextComputes s arity).andThen circleComputes))
    (pairComputes (recode (identityComputes (inputEncoding s arity)) id (fun _ => rfl) (fun _ => rfl))
      (constantComputes (inputEncoding s arity) encodingBoolBool false))

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
