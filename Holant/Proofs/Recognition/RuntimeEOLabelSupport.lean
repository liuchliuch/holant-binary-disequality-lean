import Holant.Proofs.Recognition.RuntimeEOSupportCorrectness
import Holant.Proofs.Recognition.RuntimeEOCriterionNormalization

/-! Compose actual central/completed view support with the runtime EO scans.
The source table is the previously retained original-root support output;
all table laws are derived here, rather than supplied as evaluator assumptions.
The final family/profile controller and literal A/P tests remain separate. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOLabelSupport
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Hardness
open CommonFieldMachine (Executes)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def checks (r : RuntimeEOViewSupport.Input) : RuntimeEOSupportCheck.Output :=
  RuntimeEOSupportCheck.output (RuntimeEOViewSupport.table r)
def executes : Executes RuntimeEOViewSupport.encoding RuntimeEOSupportCheck.outputEncoding checks :=
  RuntimeEOViewSupport.executes.comp RuntimeEOSupportCheck.executes

def centralInput (d : RuntimeSupportTable.LabelData) : RuntimeEOViewSupport.Input :=
  ((d.1.arity d.2,false,0),RuntimeSupportTable.labelOutput d)
def completedInput (d : RuntimeSupportTable.LabelData) (k : ℕ) : RuntimeEOViewSupport.Input :=
  ((d.1.arity d.2,true,k),RuntimeSupportTable.labelOutput d)
def native (d : RuntimeSupportTable.LabelData) := sourceKBasis.symm.action (d.1.G d.2)
def centralSignature (d : RuntimeSupportTable.LabelData) := Signature.centralRestriction (native d)
def completedSignature (d : RuntimeSupportTable.LabelData) (k : ℕ) := SingleWeightCompletion.completed (native d) k

def centralZero (d : RuntimeSupportTable.LabelData) (x : Fin (d.1.arity d.2) → Bool) : Bool :=
  RuntimeEOViewSupport.zero (centralInput d) (List.ofFn x)
def completedZero (d : RuntimeSupportTable.LabelData) (k : ℕ)
    (x : Fin (d.1.arity d.2+SingleWeightCompletion.extra (d.1.arity d.2) k) → Bool) : Bool :=
  RuntimeEOViewSupport.zero (completedInput d k) (List.ofFn x)

theorem central_zero (d : RuntimeSupportTable.LabelData) (x : Fin (d.1.arity d.2) → Bool) :
    centralZero d x=true ↔ centralSignature d x=0 := RuntimeEOViewSupport.central_zero d 0 x

theorem completed_zero (d : RuntimeSupportTable.LabelData) (k : ℕ)
    (x : Fin (d.1.arity d.2+SingleWeightCompletion.extra (d.1.arity d.2) k) → Bool) :
    completedZero d k x=true ↔ completedSignature d k x=0 := RuntimeEOViewSupport.completed_zero d k x

theorem central_table (d : RuntimeSupportTable.LabelData) :
    RuntimeEOViewSupport.table (centralInput d)=RuntimeEOSupportCorrectness.source (centralZero d) := by
  simp only [RuntimeEOViewSupport.table,centralInput,RuntimeEOView.arity,Bool.false_eq_true,ite_false,
    RationalTableMachine.words_eq,List.map_map,Function.comp_def,RuntimeEOSupportCorrectness.source,centralZero]

theorem completed_table (d : RuntimeSupportTable.LabelData) (k : ℕ) :
    RuntimeEOViewSupport.table (completedInput d k)=RuntimeEOSupportCorrectness.source (completedZero d k) := by
  simp only [RuntimeEOViewSupport.table,completedInput,RuntimeEOView.arity,ite_true,
    RationalTableMachine.words_eq,List.map_map,Function.comp_def,RuntimeEOSupportCorrectness.source,completedZero]

theorem central_domain (d : RuntimeSupportTable.LabelData) : (checks (centralInput d)).1=[] ↔
    Signature.CentralSupport (centralSignature d) := by
  change RuntimeEOSupportCheck.domainFailures (RuntimeEOViewSupport.table (centralInput d))=[] ↔ _
  rw [central_table]
  exact RuntimeEOSupportCorrectness.domain_empty (centralZero d) (centralSignature d) (central_zero d)

theorem completed_domain (d : RuntimeSupportTable.LabelData) (k : ℕ) : (checks (completedInput d k)).1=[] ↔
    Signature.CentralSupport (completedSignature d k) := by
  change RuntimeEOSupportCheck.domainFailures (RuntimeEOViewSupport.table (completedInput d k))=[] ↔ _
  rw [completed_table]
  exact RuntimeEOSupportCorrectness.domain_empty (completedZero d k) (completedSignature d k) (completed_zero d k)

def failures (negative : Bool) (r : RuntimeEOSupportCheck.Output) := if negative then r.2.1 else r.2.2

theorem failures_check (negative : Bool) (r : RuntimeEOViewSupport.Input) :
    failures negative (checks r)=RuntimeEOSupportCheck.tripleFailures negative (RuntimeEOViewSupport.table r) := by
  cases negative <;> rfl

theorem central_sign (negative : Bool) (d : RuntimeSupportTable.LabelData) :
    failures negative (checks (centralInput d))=[] ↔
    ∀a b c,centralSignature d a≠0 → centralSignature d b≠0 → centralSignature d c≠0 →
      centralSignature d (tripleXor a b c)≠0 ∨
        0<(RuntimeEOSupportCorrectness.signOf negative).value*Holant.charge (tripleXor a b c) := by
  rw [failures_check,central_table]
  exact RuntimeEOSupportCorrectness.triples_empty (centralZero d) (centralSignature d) (central_zero d) negative

theorem completed_sign (negative : Bool) (d : RuntimeSupportTable.LabelData) (k : ℕ) :
    failures negative (checks (completedInput d k))=[] ↔
    ∀a b c,completedSignature d k a≠0 → completedSignature d k b≠0 → completedSignature d k c≠0 →
      completedSignature d k (tripleXor a b c)≠0 ∨
        0<(RuntimeEOSupportCorrectness.signOf negative).value*Holant.charge (tripleXor a b c) := by
  rw [failures_check,completed_table]
  exact RuntimeEOSupportCorrectness.triples_empty (completedZero d k) (completedSignature d k) (completed_zero d k) negative

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOLabelSupport
