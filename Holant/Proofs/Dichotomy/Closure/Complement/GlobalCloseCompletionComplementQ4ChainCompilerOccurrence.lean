import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerLocalRows
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Assemble

/-! Actual marked-row parsing with two fresh edge IDs per chain link. The
prefix counter reads only earlier original labels, preserving occurrence order. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerOccurrence
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution RawClosedNetwork
open UniversalPairReduction.SmoothingCompiler Holant.OneHot.StackProgram.GraphLabelEncoding
namespace B
export Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
  (Input inputEncoding Query queryEncoding contextComputes indexComputes lengthComputes sourceComputes
   originalQuery originalQueryComputes originalRowComputes before beforeComputes multiplyComputes marked markedComputes
   queriesEncoding queriesComputes allRowsComputes repeatEdgesComputes)
end B
export B (Input inputEncoding Query queryEncoding contextComputes indexComputes lengthComputes sourceComputes
  originalQuery originalQueryComputes originalRowComputes before beforeComputes multiplyComputes marked markedComputes
  queriesEncoding queriesComputes allRowsComputes repeatEdgesComputes)
namespace L
export GlobalCloseCompletionComplementQ4ChainCompilerLocalRows (LocalInput localEncoding placedRows rowsComputes)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s b : ℕ) (arity : ℕ→ℕ)

def offset (distinguished : ℕ) (x : Query s b arity) : ℕ:=
  x.1.2.val.edges.length+(2*x.1.1)*before s b arity distinguished x

def offsetComputes (distinguished : ℕ) : Computes (queryEncoding s b arity)
    encodingNatBool (offset s b arity distinguished) := by
  let twice := (pairComputes (constantComputes (queryEncoding s b arity) encodingNatBool 2)
    ((lengthComputes s b arity).andThen UnaryBinary.computes)).andThen multiplyComputes
  exact (pairComputes
    (((sourceComputes s b arity).andThen
      (FixedGadgetSubstitution.Compiler.edgeCountComputes s b arity)).andThen UnaryBinary.computes)
    ((pairComputes twice ((beforeComputes s b arity distinguished).andThen UnaryBinary.computes)).andThen
      multiplyComputes)).andThen FixedGadgetSubstitution.Compiler.addComputes

def placement (distinguished : ℕ) (x : Query s b arity) : L.LocalInput:=
  (x.1.1,(offset s b arity distinguished x,(x.1.2.val.vertices.get x.2).2))

def placementComputes (distinguished : ℕ) : Computes (queryEncoding s b arity)
    L.localEncoding (placement s b arity distinguished) :=
  pairComputes (lengthComputes s b arity)
    (pairComputes (offsetComputes s b arity distinguished)
      ((originalRowComputes s b arity).andThen
        (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
          id (fun _=>rfl) (fun _=>rfl))))

def rows (distinguished label : ℕ) (x : Query s b arity) : List RawVertex:=
  if marked s b arity distinguished x then L.placedRows label (placement s b arity distinguished x)
    else [x.1.2.val.vertices.get x.2]

def rowChunkComputes (distinguished label : ℕ) : Computes (queryEncoding s b arity)
    Frame.wordEncoding (fun x=>FixedGadgetSubstitution.Compiler.entries vertexEncoding
      (rows s b arity distinguished label x)) := by
  let yes:=((placementComputes s b arity distinguished).andThen (L.rowsComputes label)).andThen
    (FixedGadgetSubstitution.Compiler.entriesComputes vertexEncoding)
  let no:=(originalRowComputes s b arity).andThen (FixedGadgetSubstitution.Compiler.entryComputes vertexEncoding)
  refine congrComputes (ifComputes (markedComputes s b arity distinguished) yes no) ?_
  intro x
  cases h : marked s b arity distinguished x <;> simp [rows,h,FixedGadgetSubstitution.Compiler.entries]

def doubleUnaryComputes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun k=>2*k) :=
  recode (FixedGadgetSubstitution.Compiler.joinComputes (FixedGadgetSubstitution.Compiler.encodeComputes UnaryBinary.unaryEncoding)
    (FixedGadgetSubstitution.Compiler.encodeComputes UnaryBinary.unaryEncoding)) id (fun _=>rfl)
    (fun k=>by
      change List.replicate k true++List.replicate k true=List.replicate (2*k) true
      rw [two_mul,List.replicate_add])


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerOccurrence
end
