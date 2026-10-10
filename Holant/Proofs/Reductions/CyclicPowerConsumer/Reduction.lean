import Holant.Proofs.Reductions.CyclicPowerConsumer.Macro
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget


noncomputable section
namespace Holant.LocalDrafts.Hardness.CyclicPowerConsumer
open Holant.Tractable
open scoped BigOperators
open Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain RingHomRealization
open CyclicBoundary CyclicBoundary.AlgebraicRepresentatives
open Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant.Complexity.FixedGadgetSubstitution.Compiler
set_option backward.isDefEq.respectTransparency false
open GeneralExtraction
namespace Machine

variable {s N : ℕ} {arity : ℕ → ℕ} {F : SignatureFamily ℂ}
variable {R : PhysicalAttachments.Representatives F N} {q : Signature ℂ 4}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (d : CountedDoubled R q)
variable (hl : ∀ v, (⟨d.certificate.circuit.network.shape.arity v,
  d.certificate.circuit.network.vertex v⟩ : AnySignature ℂ) ∈ mapFamily inclusion (family G))
variable (hN : 0 < N) (ha : arity s = 2)

abbrev b := machineFactor G d hl hN ha
abbrev sourceMacro := machineMacro G d hl hN ha
abbrev field := GeneralCommonField.field G (b G d hl hN ha) (sourceMacro G d hl hN ha)
abbrev presentation := GeneralCommonField.presentation G (b G d hl hN ha) (sourceMacro G d hl hN ha)
abbrev original := GeneralCommonField.original G (b G d hl hN ha) (sourceMacro G d hl hN ha)
abbrev factor := GeneralCommonField.factor G (b G d hl hN ha) (sourceMacro G d hl hN ha)
abbrev commonMacro := GeneralCommonField.powerMacro G (b G d hl hN ha) (sourceMacro G d hl hN ha)
abbrev sourceValue := GeneralCommonField.sourceValue G (b G d hl hN ha) (sourceMacro G d hl hN ha)
abbrev targetValue := GeneralOriginalTarget.originalValue G
abbrev targetPresentation := GeneralOriginalTarget.originalPresentation G
abbrev inputEncoding := GeneralFieldReduction.inputEncoding (s:=s) (arity:=arity)
abbrev queryEncoding := GeneralFieldReduction.queryEncoding (s:=s) (arity:=arity)
abbrev embedding := GeneralOriginalTarget.embedding G (b G d hl hN ha) (sourceMacro G d hl hN ha)

/-- Direct instantiation of the already delivered composed reduction. -/
def composed := GeneralOriginalTarget.reduction G (b G d hl hN ha) (sourceMacro G d hl hN ha)

abbrev query := GeneralFieldReduction.query (original G d hl hN ha)
  (factor G d hl hN ha) (commonMacro G d hl hN ha)
abbrev queryComputes := GeneralFieldReduction.queryComputes (original G d hl hN ha)
  (factor G d hl hN ha) (commonMacro G d hl hN ha)
abbrev context := GeneralFieldReduction.context (original G d hl hN ha)
  (factor G d hl hN ha) (commonMacro G d hl hN ha)
abbrev contextEncoding := GeneralFieldReduction.contextEncoding (presentation G d hl hN ha)
abbrev pre := GeneralFieldReduction.pre (original G d hl hN ha)
  (factor G d hl hN ha) (commonMacro G d hl hN ha)
abbrev preComputes := GeneralFieldReduction.preComputes (presentation G d hl hN ha)
  (original G d hl hN ha) (factor G d hl hN ha) (commonMacro G d hl hN ha)

def answerComputes := FieldCodec.computes (targetPresentation G) (presentation G d hl hN ha)
  (embedding G d hl hN ha).toLinearMap

theorem target_inclusion (r : ExactSignatureTables.Input s 1 arity) :
    GeneralCommonField.targetValue G (b G d hl hN ha) (sourceMacro G d hl hN ha) r =
      embedding G d hl hN ha (targetValue G r) := by
  have h := TableFieldTransport.evaluate_map (targetPresentation G) (presentation G d hl hN ha)
    (embedding G d hl hN ha) (GeneralOriginalTarget.originalTables G) r
  rw [GeneralOriginalTarget.mapped_tables] at h
  exact h

def post (p : List (GeneralOriginalTarget.originalField G) ×
    GeneralFieldReduction.Context (field G d hl hN ha)) : field G d hl hN ha :=
  GeneralFieldReduction.correction (original G d hl hN ha) (factor G d hl hN ha)
    (commonMacro G d hl hN ha) (embedding G d hl hN ha (p.1.getD 0 0),p.2)

def postComputes : Computes
    (OracleBatch.contextEncoding (targetPresentation G).encoding (contextEncoding G d hl hN ha))
    (presentation G d hl hN ha).encoding (post G d hl hN ha) :=
  (pairComputes
    (((Wiring.firstComputes (framedListEncoding (targetPresentation G).encoding)
      (contextEncoding G d hl hN ha)).andThen (getDComputes (targetPresentation G).encoding 0 0)).andThen
        (answerComputes G d hl hN ha))
    (Wiring.secondComputes (framedListEncoding (targetPresentation G).encoding)
      (contextEncoding G d hl hN ha))).andThen
    (GeneralFieldReduction.correctionComputes (presentation G d hl hN ha)
      (original G d hl hN ha) (factor G d hl hN ha) (commonMacro G d hl hN ha))

theorem recovery (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    sourceValue G d hl hN ha r = post G d hl hN ha
      (OracleBatch.answers (targetValue G) (pre G d hl hN ha r)) := by
  change sourceValue G d hl hN ha r = GeneralFieldReduction.correction
    (original G d hl hN ha) (factor G d hl hN ha) (commonMacro G d hl hN ha)
    (embedding G d hl hN ha (targetValue G (query G d hl hN ha r)),context G d hl hN ha r)
  rw [←target_inclusion G d hl hN ha]
  exact GeneralFieldReduction.recovery (presentation G d hl hN ha)
    (original G d hl hN ha) (factor G d hl hN ha) (commonMacro G d hl hN ha) r

/-- Same actual query compiler, with the original-G oracle's answer codec. -/
def reduction : PolyTimeOracleReduction (inputEncoding (s:=s) (arity:=arity))
    (presentation G d hl hN ha).encoding (queryEncoding (s:=s) (arity:=arity))
    (targetPresentation G).encoding (sourceValue G d hl hN ha) (targetValue G) :=
  OracleBatch.of_eq (preComputes G d hl hN ha) (postComputes G d hl hN ha)
    ((GeneralOriginalTarget.originalTables G).outputBound (targetPresentation G))
    (sourceValue G d hl hN ha) (recovery G d hl hN ha)

def controlled : LengthControlledOracleReduction (inputEncoding (s:=s) (arity:=arity))
    (presentation G d hl hN ha).encoding (queryEncoding (s:=s) (arity:=arity))
    (targetPresentation G).encoding (sourceValue G d hl hN ha) (targetValue G) := by
  have he : sourceValue G d hl hN ha = fun r => post G d hl hN ha
      (OracleBatch.answers (targetValue G) (pre G d hl hN ha r)) := funext (recovery G d hl hN ha)
  rw [he]
  exact TraceQueryControl.controlledBatch (preComputes G d hl hN ha) (postComputes G d hl hN ha)
    ((GeneralOriginalTarget.originalTables G).outputBound (targetPresentation G))

theorem target_exact (r : ExactSignatureTables.Input s 1 arity) :
    (targetValue G r : AlgebraicComplex) =
      (r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0 :=
  GeneralOriginalTarget.target_exact G r

theorem source_exact (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    (sourceValue G d hl hN ha r : AlgebraicComplex) =
      Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.ResidueAnchors.value
        (GeneralOriginalQuery.factorTable G (b G d hl hN ha)) r :=
  GeneralCommonField.source_table_exact G (b G d hl hN ha) (sourceMacro G d hl hN ha) r

theorem source_graph_exact (r : GeneralOriginalQuery.Input (s:=s) (arity:=arity)) :
    (sourceValue G d hl hN ha r : AlgebraicComplex) =
      (r.val.realize r.property
        (Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Tables.typed
          (GeneralOriginalQuery.factorTable G (b G d hl hN ha)) (s+1) arity)
        (fun _ => Signature.disequality)).denote Fin.elim0 :=
  GeneralCommonField.source_exact G (b G d hl hN ha) (sourceMacro G d hl hN ha) r

/-- The new label is the physical single binary with its two original ports. -/
theorem factor_entry (x : Fin (arity s) → Bool) :
    inclusion ((factor G d hl hN ha x : field G d hl hN ha) : AlgebraicComplex) =
      ActualCards.physical₂ (DihedralFactor.anti d.ratio)
        (fun i => x (Fin.cast ha.symm i)) := by
  change inclusion (castFactor ha.symm (CyclicPowerConsumer.factor G d hl hN) x) = _
  rw [castFactor_apply]
  exact congrFun (factor_embedding G d hl hN) (fun i => x (Fin.cast ha.symm i))

end Machine
end Holant.LocalDrafts.Hardness.CyclicPowerConsumer
