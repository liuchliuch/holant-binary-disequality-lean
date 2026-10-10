import Holant.Proofs.Recognition.RuntimeEOResultSummary
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOSupportCheck

/-! Physical family-wide EO domain/two-sign aggregation. The same sign is
chosen outside the label universal. All actual bad-word/triple lists remain in
the returned packet; this finishing stage does not call an algebraic search. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOResultSummary
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck (Output outputEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Summary := Bool × (Bool × Bool)
abbrev summaryTailEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev summaryEncoding := pairEncoding encodingBoolBool summaryTailEncoding
abbrev LabelResult := ℕ × Output
abbrev labelEncoding := pairEncoding encodingNatBool outputEncoding
abbrev familyEncoding := framedListEncoding labelEncoding
abbrev Result := Summary × List LabelResult
abbrev resultEncoding := pairEncoding summaryEncoding familyEncoding

def localFlags (o : Output) : Summary := (o.1.isEmpty,o.2.1.isEmpty,o.2.2.isEmpty)
def flags (rs : List LabelResult) : Summary :=
  (rs.all (fun r => (localFlags r.2).1),rs.all (fun r => (localFlags r.2).2.1),rs.all (fun r => (localFlags r.2).2.2))
def finish (rs : List LabelResult) : Result := (flags rs,rs)
def accepts (r : Result) : Bool := r.1.1 && (r.1.2.1 || r.1.2.2)

def emptyComputes {A : Type} (ea : Encoding A Bool) : Computes (framedListEncoding ea) encodingBoolBool List.isEmpty := by
  let raw := (WireLists.mapComputes ea encodingBoolBool (fun _ : A => false)
    (constantComputes ea encodingBoolBool false)).andThen ResidueCells.all
  exact congrComputes raw (fun xs => by cases xs <;> simp)

def localComputes : Computes outputEncoding summaryEncoding localFlags := by
  let dom := Wiring.firstComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.tableEncoding
    (pairEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.triplesEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.triplesEncoding)
  let both := Wiring.secondComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.tableEncoding
    (pairEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.triplesEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.triplesEncoding)
  let pos := both.andThen (Wiring.firstComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.triplesEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.triplesEncoding)
  let neg := both.andThen (Wiring.secondComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.triplesEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.triplesEncoding)
  exact pairComputes (dom.andThen (emptyComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.zeroRowEncoding))
    (pairComputes (pos.andThen (emptyComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.tripleEncoding))
      (neg.andThen (emptyComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.tripleEncoding)))

def flagsComputes : Computes familyEncoding summaryEncoding flags := by
  let labelFlags := (Wiring.secondComputes encodingNatBool outputEncoding).andThen localComputes
  let dom := labelFlags.andThen (Wiring.firstComputes encodingBoolBool summaryTailEncoding)
  let both := labelFlags.andThen (Wiring.secondComputes encodingBoolBool summaryTailEncoding)
  let pos := both.andThen (Wiring.firstComputes encodingBoolBool encodingBoolBool)
  let neg := both.andThen (Wiring.secondComputes encodingBoolBool encodingBoolBool)
  let all {f : LabelResult → Bool} (w : Computes labelEncoding encodingBoolBool f) :=
    (WireLists.mapComputes labelEncoding encodingBoolBool f w).andThen ResidueCells.all
  exact congrComputes (pairComputes (all dom) (pairComputes (all pos) (all neg)))
    (fun rs => by simp only [flags,List.all_map,Function.comp_def,id_eq])

def computes : Computes familyEncoding resultEncoding finish :=
  pairComputes flagsComputes (identityComputes familyEncoding)

def acceptsComputes : Computes resultEncoding encodingBoolBool accepts := by
  let summary := Wiring.firstComputes summaryEncoding familyEncoding
  let op := FiniteRecode.computes summaryEncoding encodingBoolBool
    (fun p : Summary => p.1 && (p.2.1 || p.2.2)) 32
    (by rintro ⟨a,b,c⟩; cases a <;> cases b <;> cases c <;> decide)
  exact summary.andThen op

theorem domain_correct (rs : List LabelResult) : (flags rs).1=true ↔ ∀r∈rs,r.2.1=[] := by
  simp only [flags,localFlags,List.all_eq_true,List.isEmpty_iff]
theorem positive_correct (rs : List LabelResult) : (flags rs).2.1=true ↔ ∀r∈rs,r.2.2.1=[] := by
  simp only [flags,localFlags,List.all_eq_true,List.isEmpty_iff]
theorem negative_correct (rs : List LabelResult) : (flags rs).2.2=true ↔ ∀r∈rs,r.2.2.2=[] := by
  simp only [flags,localFlags,List.all_eq_true,List.isEmpty_iff]

theorem accepts_correct (rs : List LabelResult) : accepts (finish rs)=true ↔
    (∀r∈rs,r.2.1=[]) ∧ ((∀r∈rs,r.2.2.1=[]) ∨ (∀r∈rs,r.2.2.2=[])) := by
  simp only [accepts,finish,Bool.and_eq_true,Bool.or_eq_true,domain_correct,positive_correct,negative_correct]

theorem retained (rs : List LabelResult) : (finish rs).2=rs := rfl

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOResultSummary
