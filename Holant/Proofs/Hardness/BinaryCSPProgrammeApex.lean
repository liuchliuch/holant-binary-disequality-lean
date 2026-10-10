import Holant.Proofs.Hardness.BinaryCSPProgrammeMixed
import Holant.Proofs.Hardness.BinaryIsingRaw

/-! Physical three-row apex construction, aligned first-pair polarity tape,
and strictly positive repetition. All declared old variables are retained,
including isolated variables and the empty input graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeApex
open Turing Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open BinaryCSPProgrammeCore
open UniversalPairReduction.SmoothingCompiler
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace I
export BinaryIsingRaw (apexRaw polarities expanded expandedPolarities expanded_valid)
end I
namespace M
export BinaryCSPProgrammeMixed (Input inputEncoding query queryComputes mixedValue preprocessing pre)
end M
namespace A
export Holant.LocalDrafts.Tractability.AffineMachine.AccessPrograms (flatMap)
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (list₃)
end A
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (tabulate flatten succComputes)
end W
namespace N
export BinaryCSPProgrammeNative (targetValue tables post)
end N
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (TargetInput targetEncoding)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

abbrev polaritiesEncoding := BinaryCSPProgrammeMixedRecords.polaritiesEncoding
abbrev rawQueryEncoding := pairEncoding encoding unary
abbrev Query := P.Input×ℕ
abbrev queryEncoding := pairEncoding P.inputEncoding unary

def binarySucc : Computes encodingNatBool encodingNatBool (fun n=>n+1) :=
  ((pairComputes (identityComputes encodingNatBool) (constantComputes encodingNatBool encodingNatBool 1)).andThen
    Endpoints.prepareArithmeticComputes).andThen BinaryCompose.additionComputes

def apexRowComputes : Computes edgeEncoding edgesEncoding
    (fun e=>[(e.1+1,0),(e.2+1,0),(e.1+1,e.2+1)]) := by
  let left := (Wiring.firstComputes encodingNatBool encodingNatBool).andThen binarySucc
  let right := (Wiring.secondComputes encodingNatBool encodingNatBool).andThen binarySucc
  let zero := constantComputes edgeEncoding encodingNatBool 0
  exact A.list₃ edgeEncoding (pairComputes left zero) (pairComputes right zero) (pairComputes left right)

def apexComputes : Computes encoding encoding I.apexRaw :=
  assemble (variablesComputes.andThen W.succComputes)
    (edgesComputes.andThen (A.flatMap edgeEncoding edgeEncoding _ apexRowComputes))
    (constantComputes encoding signsEncoding [])

def polaritiesComputes : Computes encoding polaritiesEncoding I.polarities :=
  edgesComputes.andThen (A.flatMap edgeEncoding encodingBoolBool (fun _=>[false,false,true])
    (constantComputes edgeEncoding polaritiesEncoding [false,false,true]))

def expandedComputes : Computes rawQueryEncoding encoding (fun a=>I.expanded a.1 a.2) :=
  (pairComputes ((Wiring.firstComputes encoding unary).andThen apexComputes)
    (Wiring.secondComputes encoding unary)).andThen BinaryCSPProgrammeRepeat.repeatComputes

def polarityCopiesComputes : Computes (pairEncoding unary encodingBoolBool) polaritiesEncoding
    (fun a=>List.replicate (a.1+1) a.2) := by
  let source := pairEncoding unary encodingBoolBool
  let count := (Wiring.firstComputes unary encodingBoolBool).andThen W.succComputes
  let cell := (Wiring.firstComputes source unary).andThen (Wiring.secondComputes unary encodingBoolBool)
  exact congrComputes (W.tabulate source encodingBoolBool (fun a=>a.1+1) count
    (fun a _=>a.2) cell) (fun a=>by simp)

def expandedPolaritiesComputes : Computes rawQueryEncoding polaritiesEncoding
    (fun a=>I.expandedPolarities a.1 a.2) := by
  let raw := Wiring.firstComputes encoding unary
  let k := Wiring.secondComputes encoding unary
  let chunks := (pairComputes k (raw.andThen polaritiesComputes)).andThen
    (UniversalPairReduction.SmoothingCompiler.mapListComputes unary encodingBoolBool polaritiesEncoding
      (fun n b=>List.replicate (n+1) b) polarityCopiesComputes)
  exact congrComputes (chunks.andThen (W.flatten encodingBoolBool)) (fun _=>(List.flatMap_def).symm)

def expand (a : Query) : M.Input :=
  (⟨I.expanded a.1.val a.2,I.expanded_valid a.1.val a.1.property a.2⟩,I.expandedPolarities a.1.val a.2)

def computes : Computes queryEncoding M.inputEncoding expand :=
  recode (pairComputes expandedComputes expandedPolaritiesComputes)
    (fun a : Query=>(a.1.val,a.2)) (fun _=>rfl) (fun _=>rfl)

def queryComputes : Computes queryEncoding O.targetEncoding (fun a=>M.query (expand a)) :=
  computes.andThen M.queryComputes

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M₀ : Signature K 4) (f : Signature K 2)

def controlled (hm : M₀=EOBinaryPlaneCore.lift f) :
    LengthControlledOracleReduction queryEncoding F.encoding O.targetEncoding F.encoding
      (fun a=>M.mixedValue f (expand a)) (N.targetValue F M₀) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch
    (computes.andThen M.pre) (N.post F) ((N.tables F M₀).outputBound F)
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho a
  rw [BinaryCSPProgrammeMixed.query_value F M₀ f hm (expand a)]
  simpa only [Function.comp_apply,M.preprocessing,OracleBatch.answers,List.map_cons,List.map_nil,
    List.getD_cons_zero,N.targetValue] using reduction.reduction.correct oracle ho a

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeApex
