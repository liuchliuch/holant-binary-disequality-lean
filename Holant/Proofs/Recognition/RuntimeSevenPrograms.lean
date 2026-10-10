import Holant.Proofs.Recognition.RuntimeFourDecision
import Holant.Proofs.Recognition.RuntimeEOViewDecision
import Holant.Proofs.Recognition.RuntimeLayerProfile

/-! The single varying-layout seven-clause controller. It computes the original
K-inverse support table once, generates every bounded profile internally, runs
one fixed central/profile EO cell, and retains all layer/domain/triple/A/P
packets. Four-clause and matching results are the actual earlier runtime
programme output. The final Boolean reads these stored flags only. Exact
seven-clause meaning is proved in the subsequent source theorem. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenPrograms
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open PhysicalFolds
open RuntimeSupportTable (Data original)
open RuntimeEOFamilySupport (Base baseEncoding sourceBase)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def tensorData (d : Data) : RuntimeTensorAggregation.Data :=
  ⟨d.count,d.arity,d.G,d.input,d.represented,false,false⟩
def eoData (d : Data) (p : Option RuntimeEOProfiles.Profile) : RuntimeEOViewDecision.Data := ⟨tensorData d,p⟩
def profiles (d : Data) := RuntimeEOProfiles.profiles (original d)
def central (d : Data) := RuntimeEOViewDecision.output (eoData d none)

abbrev ProfileDetails := RuntimeLayerProfile.Output × RuntimeEOViewDecision.Output
abbrev profileDetailsEncoding := pairEncoding RuntimeLayerProfile.outputEncoding RuntimeEOViewDecision.outputEncoding
abbrev ProfileOutput := RuntimeEOProfiles.Profile × ProfileDetails
abbrev profileOutputEncoding := pairEncoding RuntimeEOProfiles.profileEncoding profileDetailsEncoding
abbrev profilesOutputEncoding := framedListEncoding profileOutputEncoding

def profileOutput (d : Data) (p : RuntimeEOProfiles.Profile) : ProfileOutput :=
  (p,RuntimeLayerProfile.output (RuntimeLayerProfile.source d p),RuntimeEOViewDecision.output (eoData d (some p)))
def profileAccepted (p : ProfileOutput) : Bool := p.2.1.1 && p.2.2.1

def centralContextComputes : Computes baseEncoding RuntimeEOFamilySupport.encoding
    (fun r : Base => (r,(false,[]))) :=
  pairComputes (identityComputes baseEncoding) (constantComputes baseEncoding RuntimeEOFamilySupport.modeEncoding (false,[]))

def centralRuns : Runs baseEncoding RuntimeEOViewDecision.outputEncoding sourceBase central :=
  (Runs.ofComputes centralContextComputes sourceBase).comp
    (RuntimeTensorAggregation.reindexRuns RuntimeEOViewDecision.executes (fun d => eoData d none))

def profilesRuns : Runs baseEncoding RuntimeEOProfiles.outputEncoding sourceBase profiles :=
  (Runs.ofComputes (Wiring.firstComputes OriginalFamilyPackingMachine.encoding RuntimeSupportTable.resultEncoding) sourceBase).comp
    (RuntimeTensorEnumeration.ofExecutes RuntimeEOProfiles.executes original)

abbrev Cell := PromisedListMap.Cell profiles
abbrev cellEncoding := pairEncoding baseEncoding RuntimeEOProfiles.profileEncoding

def completedContextComputes : Computes cellEncoding RuntimeEOFamilySupport.encoding
    (fun r : Base × RuntimeEOProfiles.Profile => (r.1,(true,r.2))) :=
  pairComputes (Wiring.firstComputes baseEncoding RuntimeEOProfiles.profileEncoding)
    (pairComputes (constantComputes cellEncoding encodingBoolBool true)
      (Wiring.secondComputes baseEncoding RuntimeEOProfiles.profileEncoding))

def profileRuns : Runs cellEncoding profileOutputEncoding (PromisedListMap.cellInput sourceBase profiles)
    (fun d : Cell => profileOutput d.1 d.2.val) := by
  let input := PromisedListMap.cellInput sourceBase profiles
  let p := Runs.ofComputes (Wiring.secondComputes baseEncoding RuntimeEOProfiles.profileEncoding) input
  let layer := RuntimeTensorEnumeration.ofExecutes RuntimeLayerProfile.executes input
  let eo := (Runs.ofComputes completedContextComputes input).comp
    (RuntimeTensorAggregation.reindexRuns RuntimeEOViewDecision.executes (fun d : Cell => eoData d.1 (some d.2.val)))
  exact p.pair (layer.pair eo)

def allProfiles (d : Data) : List ProfileOutput := (profiles d).map (profileOutput d)
def allProfilesRuns : Runs baseEncoding profilesOutputEncoding sourceBase allProfiles :=
  ((Runs.ofComputes (identityComputes baseEncoding) sourceBase).pair profilesRuns).comp
    (PromisedListMap.mapList profileRuns)

abbrev EODetails := Base × (RuntimeEOViewDecision.Output × List ProfileOutput)
abbrev eoTailEncoding := pairEncoding RuntimeEOViewDecision.outputEncoding profilesOutputEncoding
abbrev eoDetailsEncoding := pairEncoding baseEncoding eoTailEncoding

def eoDetails (d : Data) : EODetails := (sourceBase d,central d,allProfiles d)
def eoRuns : Runs baseEncoding eoDetailsEncoding sourceBase eoDetails :=
  (Runs.ofComputes (identityComputes baseEncoding) sourceBase).pair (centralRuns.pair allProfilesRuns)

abbrev Core := EODetails × RuntimeFourDecision.Output
abbrev coreEncoding := pairEncoding eoDetailsEncoding RuntimeFourDecision.outputEncoding

def core (d : Data) : Core := (eoDetails d,RuntimeFourDecision.output (tensorData d))
def coreRuns : Runs OriginalFamilyPackingMachine.encoding coreEncoding original core :=
  (RuntimeEOFamilySupport.baseRuns.comp eoRuns).pair
    (RuntimeTensorAggregation.reindexRuns RuntimeFourDecision.executes tensorData)

abbrev Sides := Bool × Bool
abbrev sidesEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev Details := Sides × Core
abbrev detailsEncoding := pairEncoding sidesEncoding coreEncoding

def sides (p : Core) : Sides := RuntimeSupportFlags.summary p.1.1.2
def sidesExecutes : Executes coreEncoding sidesEncoding sides :=
  (Executes.ofComputes (((Wiring.firstComputes eoDetailsEncoding RuntimeFourDecision.outputEncoding).andThen
    (Wiring.firstComputes baseEncoding eoTailEncoding)).andThen
      (Wiring.secondComputes OriginalFamilyPackingMachine.encoding RuntimeSupportTable.resultEncoding))).comp
        RuntimeSupportFlags.summaryExecutes

def details (d : Data) : Details := (sides (core d),core d)
def detailsRuns : Runs OriginalFamilyPackingMachine.encoding detailsEncoding original details :=
  coreRuns.comp (RuntimeTensorEnumeration.ofExecutes
    (sidesExecutes.pair (Executes.ofComputes (identityComputes coreEncoding))) core)

def oneSided (p : Details) : Bool := (p.1.1 || p.1.2) && p.2.1.2.1.1
def singleWeight (p : Details) : Bool := (!p.1.1 && !p.1.2) && p.2.1.2.2.any profileAccepted
def matching (p : Details) : Bool := p.2.2.2.1.1.2.1
def four (p : Details) : Bool := p.2.2.1.1
def summary (p : Details) : Bool := oneSided p || singleWeight p || matching p || four p

def profileAcceptedComputes : Computes profileOutputEncoding encodingBoolBool profileAccepted := by
  let pair := Wiring.secondComputes RuntimeEOProfiles.profileEncoding profileDetailsEncoding
  let layer := (pair.andThen (Wiring.firstComputes RuntimeLayerProfile.outputEncoding RuntimeEOViewDecision.outputEncoding)).andThen
    (Wiring.firstComputes encodingBoolBool RuntimeLayerProfile.rowsEncoding)
  let eo := (pair.andThen (Wiring.secondComputes RuntimeLayerProfile.outputEncoding RuntimeEOViewDecision.outputEncoding)).andThen
    (Wiring.firstComputes encodingBoolBool RuntimeEOViewDecision.detailsEncoding)
  exact (pairComputes layer eo).andThen
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 && p.2))

def sidesComputes := Wiring.firstComputes sidesEncoding coreEncoding
def coreComputes := Wiring.secondComputes sidesEncoding coreEncoding
def eoDetailsComputes := coreComputes.andThen (Wiring.firstComputes eoDetailsEncoding RuntimeFourDecision.outputEncoding)
def eoTailComputes := eoDetailsComputes.andThen (Wiring.secondComputes baseEncoding eoTailEncoding)
def centralComputes := (eoTailComputes.andThen (Wiring.firstComputes RuntimeEOViewDecision.outputEncoding profilesOutputEncoding)).andThen
  (Wiring.firstComputes encodingBoolBool RuntimeEOViewDecision.detailsEncoding)
def profilesComputes := eoTailComputes.andThen (Wiring.secondComputes RuntimeEOViewDecision.outputEncoding profilesOutputEncoding)

def oneSidedComputes : Computes detailsEncoding encodingBoolBool oneSided :=
  (pairComputes (sidesComputes.andThen
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 || p.2))) centralComputes).andThen
      (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 && p.2))

def singleWeightComputes : Computes detailsEncoding encodingBoolBool singleWeight := by
  let both := sidesComputes.andThen
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => !p.1 && !p.2))
  let any := profilesComputes.andThen ((WireLists.mapComputes profileOutputEncoding encodingBoolBool profileAccepted
    profileAcceptedComputes).andThen ResidueCells.any)
  exact congrComputes ((pairComputes both any).andThen
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 && p.2)))
    (fun p => by simp only [singleWeight,List.any_map,Function.comp_def,id_eq])

def fourPacketComputes := coreComputes.andThen (Wiring.secondComputes eoDetailsEncoding RuntimeFourDecision.outputEncoding)
def matchingComputes : Computes detailsEncoding encodingBoolBool matching := by
  let fourDetails := fourPacketComputes.andThen
    (Wiring.secondComputes (pairEncoding encodingBoolBool encodingBoolBool) RuntimeFourDecision.detailsEncoding)
  let tensor := fourDetails.andThen
    (Wiring.firstComputes RuntimeTensorAggregation.outputEncoding RuntimeFourDecision.packetPairEncoding)
  let summary := tensor.andThen
    (Wiring.firstComputes RuntimeTensorAggregation.summaryEncoding RuntimeTensorAggregation.tripleEncoding)
  exact (summary.andThen (Wiring.secondComputes encodingBoolBool (pairEncoding encodingBoolBool encodingBoolBool))).andThen
    (Wiring.firstComputes encodingBoolBool encodingBoolBool)
def fourComputes : Computes detailsEncoding encodingBoolBool four :=
  (fourPacketComputes.andThen (Wiring.firstComputes (pairEncoding encodingBoolBool encodingBoolBool) RuntimeFourDecision.detailsEncoding)).andThen
    (Wiring.firstComputes encodingBoolBool encodingBoolBool)

def summaryComputes : Computes detailsEncoding encodingBoolBool summary := by
  let op := Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 || p.2)
  let first := (pairComputes oneSidedComputes singleWeightComputes).andThen op
  let second := (pairComputes first matchingComputes).andThen op
  exact (pairComputes second fourComputes).andThen op

abbrev Output := Bool × Details
abbrev outputEncoding := pairEncoding encodingBoolBool detailsEncoding

def output (d : Data) : Output := (summary (details d),details d)
def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding original output :=
  detailsRuns.after (pairComputes summaryComputes (identityComputes detailsEncoding))

theorem finish_control : executes.machine=detailsRuns.machine.compose
    (pairComputes summaryComputes (identityComputes detailsEncoding)).machine := rfl

theorem profiles_retained (d : Data) : (output d).2.2.1.2.2=allProfiles d := rfl

theorem profile_mem (d : Data) (p : RuntimeEOProfiles.Profile) (hp : p∈profiles d) :
    profileOutput d p∈allProfiles d := List.mem_map.mpr ⟨p,hp,rfl⟩

def source_outputs (d : Data) : TM2OutputsInTime executes.machine.computer
    (OriginalFamilyPackingMachine.encoding.encode (original d))
    (some (outputEncoding.encode (output d))) (executes.cost d) := executes.outputs d

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenPrograms
