import Holant.Proofs.Recognition.RuntimeEOLabelSupport
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOSupportCorrectness
import Holant.Proofs.Recognition.RuntimeEOCriterionNormalization

/-! Compose actual central/completed view support with the runtime EO scans.
The source table is the previously retained original-root support output;
all table laws are derived here, rather than supplied as evaluator assumptions.
The final family/profile controller and literal A/P tests remain separate. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLabelSupport
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Hardness
open CommonFieldMachine (Executes)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def checks (r : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.Input) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.Output :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.output (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.table r)
def executes : Executes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.encoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.outputEncoding checks :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.executes.comp _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.executes

def centralInput (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.Input :=
  ((d.1.arity d.2,false,0),_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelOutput d)
def completedInput (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (k : ℕ) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.Input :=
  ((d.1.arity d.2,true,k),_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelOutput d)
def native (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) := (d.1.G d.2)
def centralSignature (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) := Signature.centralRestriction (native d)
def completedSignature (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (k : ℕ) := SingleWeightCompletion.completed (native d) k

def centralZero (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (x : Fin (d.1.arity d.2) → Bool) : Bool :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.zero (centralInput d) (List.ofFn x)
def completedZero (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (k : ℕ)
    (x : Fin (d.1.arity d.2+SingleWeightCompletion.extra (d.1.arity d.2) k) → Bool) : Bool :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.zero (completedInput d k) (List.ofFn x)

theorem central_zero (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (x : Fin (d.1.arity d.2) → Bool) :
    centralZero d x=true ↔ centralSignature d x=0 := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.central_zero d 0 x

theorem completed_zero (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (k : ℕ)
    (x : Fin (d.1.arity d.2+SingleWeightCompletion.extra (d.1.arity d.2) k) → Bool) :
    completedZero d k x=true ↔ completedSignature d k x=0 := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.completed_zero d k x

theorem central_table (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) :
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.table (centralInput d)=_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.source (centralZero d) := by
  simp only [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.table,centralInput,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity,Bool.false_eq_true,ite_false,
    RationalTableMachine.words_eq,List.map_map,Function.comp_def,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.source,centralZero]

theorem completed_table (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (k : ℕ) :
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.table (completedInput d k)=_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.source (completedZero d k) := by
  simp only [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.table,completedInput,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity,ite_true,
    RationalTableMachine.words_eq,List.map_map,Function.comp_def,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.source,completedZero]

theorem central_domain (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) : (checks (centralInput d)).1=[] ↔
    Signature.CentralSupport (centralSignature d) := by
  change _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.domainFailures (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.table (centralInput d))=[] ↔ _
  rw [central_table]
  exact _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.domain_empty (centralZero d) (centralSignature d) (central_zero d)

theorem completed_domain (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (k : ℕ) : (checks (completedInput d k)).1=[] ↔
    Signature.CentralSupport (completedSignature d k) := by
  change _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.domainFailures (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.table (completedInput d k))=[] ↔ _
  rw [completed_table]
  exact _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.domain_empty (completedZero d k) (completedSignature d k) (completed_zero d k)

def failures (negative : Bool) (r : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.Output) := if negative then r.2.1 else r.2.2

theorem failures_check (negative : Bool) (r : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.Input) :
    failures negative (checks r)=_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCheck.tripleFailures negative (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOViewSupport.table r) := by
  cases negative <;> rfl

theorem central_sign (negative : Bool) (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) :
    failures negative (checks (centralInput d))=[] ↔
    ∀a b c,centralSignature d a≠0 → centralSignature d b≠0 → centralSignature d c≠0 →
      centralSignature d (tripleXor a b c)≠0 ∨
        0<(_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.signOf negative).value*Holant.charge (tripleXor a b c) := by
  rw [failures_check,central_table]
  exact _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.triples_empty (centralZero d) (centralSignature d) (central_zero d) negative

theorem completed_sign (negative : Bool) (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.LabelData) (k : ℕ) :
    failures negative (checks (completedInput d k))=[] ↔
    ∀a b c,completedSignature d k a≠0 → completedSignature d k b≠0 → completedSignature d k c≠0 →
      completedSignature d k (tripleXor a b c)≠0 ∨
        0<(_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.signOf negative).value*Holant.charge (tripleXor a b c) := by
  rw [failures_check,completed_table]
  exact _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOSupportCorrectness.triples_empty (completedZero d k) (completedSignature d k) (completed_zero d k) negative

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLabelSupport
