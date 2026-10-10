import Holant.Proofs.Recognition.RuntimeFourDecision
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeTensorAggregation

/-! The proved native four-clause controller and the specialized matching
controller share one original RootCode input and retain their actual packets. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeFourDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
open PhysicalFolds
namespace O
export Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeFourDecision
  (Output outputEncoding detailsEncoding packetPairEncoding output executes native_correct)
end O
namespace T
export Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorAggregation
  (Data family original Output outputEncoding output executes matching_correct)
end T
abbrev Output := O.Output
abbrev outputEncoding := O.outputEncoding
abbrev detailsEncoding := O.detailsEncoding
abbrev packetPairEncoding := O.packetPairEncoding
abbrev inputEncoding := pairEncoding O.outputEncoding T.outputEncoding

def pack (p : O.Output×T.Output) : Output := ((p.1.1.2,p.1.1.2),p.2,p.1.2.2)
def output (d : T.Data) : Output := pack (O.output d,T.output d)

def packComputes : Computes inputEncoding outputEncoding pack := by
  let old := Wiring.firstComputes O.outputEncoding T.outputEncoding
  let flags := old.andThen (Wiring.firstComputes (pairEncoding encodingBoolBool encodingBoolBool) O.detailsEncoding)
  let native := flags.andThen (Wiring.secondComputes encodingBoolBool encodingBoolBool)
  let details := old.andThen (Wiring.secondComputes (pairEncoding encodingBoolBool encodingBoolBool) O.detailsEncoding)
  let packets := details.andThen (Wiring.secondComputes T.outputEncoding O.packetPairEncoding)
  let tensor := Wiring.secondComputes O.outputEncoding T.outputEncoding
  exact pairComputes (pairComputes native native) (pairComputes tensor packets)

def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding T.original output :=
  (O.executes.pair T.executes).after packComputes

theorem ordinary_correct (d : T.Data) : (output d).1.1=true ↔
    TractX (familyAction sourceKBasis (T.family d)) := O.native_correct d

theorem matching_retained (d : T.Data) : (output d).2.1.1.2.1=true ↔
    MatchingAlternative (familyAction sourceKBasis (T.family d)) := T.matching_correct d


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeFourDecision
end
