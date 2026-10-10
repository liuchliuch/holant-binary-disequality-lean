import Holant.Proofs.Recognition.RuntimeEOClassFamily
import Holant.Proofs.Recognition.RuntimeEOFamilySupport

/-! Runtime EO decision for a whole central or completed view. Domain and
both-sign support traces come from the retained original support table; literal
A/P pairing searches read original RootCodes. One shared sign and one shared
class are chosen outside all label/pairing universals. The final bit reads the
same stored traces and algebraic packets. This is an intermediate promised
profile controller, not by itself the complete seven-clause source programme. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOViewDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open PhysicalFolds
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

structure Data where
  family : RuntimeTensorAggregation.Data
  profile : Option RuntimeEOProfiles.Profile

def supportData (d : Data) : RuntimeSupportTable.Data :=
  ⟨d.family.count,d.family.arity,d.family.G,d.family.input,d.family.represented⟩
def complete (d : Data) : Bool := d.profile.isSome
def layers (d : Data) : RuntimeEOProfiles.Profile := d.profile.getD []
def classData (d : Data) : RuntimeEOClassFamily.Data := ⟨d.family,complete d,layers d⟩
def source (d : Data) : RuntimeEOFamilySupport.Context :=
  RuntimeEOFamilySupport.sourceContext (supportData d) (complete d) (layers d)

def supportOutput (d : Data) := RuntimeEOFamilySupport.result (source d)
def classOutput (d : Data) := RuntimeEOClassFamily.result (classData d)
abbrev Details := RuntimeEOResultSummary.Result × RuntimeEOClassFamily.Result
abbrev detailsEncoding := pairEncoding RuntimeEOResultSummary.resultEncoding RuntimeEOClassFamily.finalEncoding

def details (d : Data) : Details := (supportOutput d,classOutput d)
def supportRuns : Runs RuntimeEOFamilySupport.encoding RuntimeEOResultSummary.resultEncoding source supportOutput :=
  RuntimeTensorEnumeration.ofExecutes RuntimeEOFamilySupport.resultExecutes source

def classInput (r : RuntimeEOFamilySupport.Context) : RuntimeEOClassFamily.Input := (r.1.1,r.2)
def classInputComputes : Computes RuntimeEOFamilySupport.encoding RuntimeEOClassFamily.encoding classInput :=
  pairComputes ((Wiring.firstComputes RuntimeEOFamilySupport.baseEncoding RuntimeEOFamilySupport.modeEncoding).andThen
    (Wiring.firstComputes OriginalFamilyPackingMachine.encoding RuntimeSupportTable.resultEncoding))
      (Wiring.secondComputes RuntimeEOFamilySupport.baseEncoding RuntimeEOFamilySupport.modeEncoding)

def classRuns : Runs RuntimeEOFamilySupport.encoding RuntimeEOClassFamily.finalEncoding source classOutput :=
  (Runs.ofComputes classInputComputes source).comp
    (RuntimeTensorAggregation.reindexRuns RuntimeEOClassFamily.resultRuns classData)
def detailsRuns : Runs RuntimeEOFamilySupport.encoding detailsEncoding source details := supportRuns.pair classRuns

def summary (p : Details) : Bool := p.1.1.1 && (p.1.1.2.1 || p.1.1.2.2) && (p.2.1.1 || p.2.1.2)
def summaryComputes : Computes detailsEncoding encodingBoolBool summary := by
  let support := Wiring.firstComputes RuntimeEOResultSummary.resultEncoding RuntimeEOClassFamily.finalEncoding
  let classes := Wiring.secondComputes RuntimeEOResultSummary.resultEncoding RuntimeEOClassFamily.finalEncoding
  let supportFlag := support.andThen RuntimeEOResultSummary.acceptsComputes
  let classFlags := classes.andThen (Wiring.firstComputes RuntimeEOClassFamily.summaryEncoding RuntimeEOClassFamily.resultEncoding)
  let classFlag := classFlags.andThen
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 || p.2))
  exact (pairComputes supportFlag classFlag).andThen
    (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 && p.2))

abbrev Output := Bool × Details
abbrev outputEncoding := pairEncoding encodingBoolBool detailsEncoding

def output (d : Data) : Output := (summary (details d),details d)
def executes : Runs RuntimeEOFamilySupport.encoding outputEncoding source output :=
  detailsRuns.after (pairComputes summaryComputes (identityComputes detailsEncoding))

def arity (d : Data) (i : Fin d.family.count) : ℕ :=
  RuntimeEOView.arity (d.family.arity i,complete d,(layers d).getD i.val 0)
def signatures (d : Data) (i : Fin d.family.count) : Signature AlgebraicComplex (arity d i) :=
  RuntimeEOLiteralTable.viewSignature (d.family.G i) (complete d) ((layers d).getD i.val 0)
def family (d : Data) := RuntimeEOCriterionNormalization.family (arity d) (signatures d)

theorem domain_correct (d : Data) : (supportOutput d).1.1=true ↔
    RuntimeEOCriterionNormalization.Domain (arity d) (signatures d) := by
  rcases d with ⟨f,p⟩
  cases p with
  | none => exact RuntimeEOFamilySupport.central_domain (supportData ⟨f,none⟩)
  | some p => exact RuntimeEOFamilySupport.completed_domain (supportData ⟨f,some p⟩) p

theorem sign_correct (negative : Bool) (d : Data) :
    RuntimeEOFamilySupport.signFlag negative (supportOutput d)=true ↔
      RuntimeEOCriterionNormalization.Triples (arity d) (signatures d) (RuntimeEOSupportCorrectness.signOf negative) := by
  rcases d with ⟨f,p⟩
  cases p with
  | none => exact RuntimeEOFamilySupport.central_sign negative (supportData ⟨f,none⟩)
  | some p => exact RuntimeEOFamilySupport.completed_sign negative (supportData ⟨f,some p⟩) p

theorem affine_correct (d : Data) : (classOutput d).1.1=true ↔
    RuntimeEOCriterionNormalization.Classes (arity d) (signatures d) .affine :=
  RuntimeEOClassFamily.affine_correct (classData d)
theorem product_correct (d : Data) : (classOutput d).1.2=true ↔
    RuntimeEOCriterionNormalization.Classes (arity d) (signatures d) .product :=
  RuntimeEOClassFamily.product_correct (classData d)

theorem output_correct (d : Data) : (output d).1=true ↔ EOTract (preprocess (family d)) := by
  change (output d).1=true ↔ EOTract (preprocess (RuntimeEOCriterionNormalization.family (arity d) (signatures d)))
  rw [RuntimeEOCriterionNormalization.criterion_iff]
  change ((supportOutput d).1.1 && ((supportOutput d).1.2.1 || (supportOutput d).1.2.2) &&
    ((classOutput d).1.1 || (classOutput d).1.2))=true ↔ _
  simp only [Bool.and_eq_true,Bool.or_eq_true,domain_correct,affine_correct,product_correct]
  have hp := sign_correct true d
  have hn := sign_correct false d
  change (supportOutput d).1.2.1=true ↔ RuntimeEOCriterionNormalization.Triples (arity d) (signatures d) .positive at hp
  change (supportOutput d).1.2.2=true ↔ RuntimeEOCriterionNormalization.Triples (arity d) (signatures d) .negative at hn
  rw [hp,hn]
  constructor
  · rintro ⟨⟨hd,hs⟩,hc⟩
    refine ⟨hd,?_⟩
    rcases hs with hp | hn <;> rcases hc with ha | hpr
    · exact ⟨.positive,.affine,hp,ha⟩
    · exact ⟨.positive,.product,hp,hpr⟩
    · exact ⟨.negative,.affine,hn,ha⟩
    · exact ⟨.negative,.product,hn,hpr⟩
  · rintro ⟨hd,sign,C,hs,hc⟩
    cases sign <;> cases C
    · exact ⟨⟨hd,Or.inl hs⟩,Or.inl hc⟩
    · exact ⟨⟨hd,Or.inl hs⟩,Or.inr hc⟩
    · exact ⟨⟨hd,Or.inr hs⟩,Or.inl hc⟩
    · exact ⟨⟨hd,Or.inr hs⟩,Or.inr hc⟩

theorem output_false_iff (d : Data) : (output d).1=false ↔ ¬EOTract (preprocess (family d)) := by
  have hb : ∀b : Bool,b=false ↔ ¬b=true := by intro b; cases b <;> simp
  rw [hb,output_correct]

theorem support_retained (d : Data) : (output d).2.1=supportOutput d := rfl
theorem classes_retained (d : Data) : (output d).2.2=classOutput d := rfl
theorem finishing_control : executes.machine=detailsRuns.machine.compose
    (pairComputes summaryComputes (identityComputes detailsEncoding)).machine := rfl

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOViewDecision
