import Holant.Proofs.Dichotomy.Main.PaperBinaryDisequalityDecision
import Holant.Proofs.Dichotomy.Main.PaperLiteralEqualityDecision
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecisionSource

/-! Exact-input decision entries for the three main manuscript theorems.

Each existential machine precedes every family size, arity layout, signature
table and representing RootCode input. All three programmes read the original
coefficient descriptors. Their output encodings and actual execution costs
are retained; no polynomial-time criterion-recognition bound is asserted.

The first two criteria are the four-clause predicates, respectively with and
without the literal identity adjoined. The third is the full seven-clause
predicate after forward K on the unchanged original family.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (input : OriginalFamilyInput.Input (fun i : Fin s => a i.val))
variable (represented : ∀ i x, (input i x).Represents (G i x : ℂ))

/-- The third decision programme receives the same original indexed family
as the third complexity theorem, with no transformed input or supplied I. -/
def quaternaryData : PaperQuaternaryDecisionSource.Data where
  count := s
  arity i := a i.val
  G := G
  input := input
  represented := represented

theorem quaternary_family_exact :
    PaperQuaternaryDecisionSource.family (quaternaryData G input represented) =
      PaperLiteralEqualityCriterion.family G := rfl

theorem quaternary_original_exact :
    PaperQuaternaryDecisionSource.original (quaternaryData G input represented) =
      OriginalFamilyPackingSource.fromSource (fun i : Fin s => a i.val) input false := rfl

theorem quaternary_decision_correct :
    PaperQuaternaryDecisionSource.answer (quaternaryData G input represented) = true ↔
      Tract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G)) :=
  PaperQuaternaryDecisionSource.answer_correct (quaternaryData G input represented)

theorem quaternary_decision_false_iff :
    PaperQuaternaryDecisionSource.answer (quaternaryData G input represented) = false ↔
      ¬Tract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G)) :=
  PaperQuaternaryDecisionSource.answer_false_iff (quaternaryData G input represented)

/-- Decision assertion of manuscript Theorem 1, line 309:
one machine decides TractX(K(F union {I})) from original exact input. -/
theorem binaryDisequality_uniform : ∃ M : BinaryCompose.Machine,
    ∀ (s : ℕ) (a : ℕ → ℕ)
      (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
      (input : OriginalFamilyInput.Input (fun i : Fin s => a i.val))
      (represented : ∀ i x, (input i x).Represents (G i x : ℂ)),
      Nonempty (TM2OutputsInTime M.computer
        (OriginalFamilyPackingMachine.encoding.encode
          (OriginalFamilyPackingSource.fromSource (fun i : Fin s => a i.val) input false))
        (some (RuntimeAugmentedNativeDecision.outputEncoding.encode
          (RuntimeAugmentedNativeDecision.output (PaperBinaryDisequalityDecision.data G input represented))))
        (RuntimeAugmentedNativeDecision.executes.cost
          (PaperBinaryDisequalityDecision.data G input represented))) ∧
      (RuntimeAugmentedNativeDecision.answer (PaperBinaryDisequalityDecision.data G input represented) = true ↔
        TractX (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G ∪
          {(⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)}))) :=
  PaperBinaryDisequalityDecision.uniform

/-- Decision assertion of manuscript Theorem 2, line 320:
one machine decides TractX(KF) from the unchanged original exact input. -/
theorem literalEquality_uniform : ∃ M : BinaryCompose.Machine,
    ∀ (s : ℕ) (a : ℕ → ℕ)
      (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
      (input : OriginalFamilyInput.Input (fun i : Fin s => a i.val))
      (represented : ∀ i x, (input i x).Represents (G i x : ℂ)),
      Nonempty (TM2OutputsInTime M.computer
        (OriginalFamilyPackingMachine.encoding.encode
          (OriginalFamilyPackingSource.fromSource (fun i : Fin s => a i.val) input false))
        (some (RuntimeFourDecision.outputEncoding.encode
          (RuntimeFourDecision.output (PaperLiteralEqualityDecision.data G input represented))))
        (RuntimeFourDecision.executes.cost (PaperLiteralEqualityDecision.data G input represented))) ∧
      (PaperLiteralEqualityDecision.answer G input represented = true ↔
        TractX (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G))) :=
  PaperLiteralEqualityDecision.uniform

/-- Decision assertion of manuscript Theorem 3, line 339:
one machine decides full Tract(KF) across all original RootCode layouts. -/
theorem quaternary_uniform : ∃ M : BinaryCompose.Machine,
    ∀ (s : ℕ) (a : ℕ → ℕ)
      (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
      (input : OriginalFamilyInput.Input (fun i : Fin s => a i.val))
      (represented : ∀ i x, (input i x).Represents (G i x : ℂ)),
      Nonempty (TM2OutputsInTime M.computer
        (OriginalFamilyPackingMachine.encoding.encode
          (OriginalFamilyPackingSource.fromSource (fun i : Fin s => a i.val) input false))
        (some (PaperQuaternaryDecision.RuntimeSevenPrograms.outputEncoding.encode
          (PaperQuaternaryDecision.RuntimeSevenPrograms.output (quaternaryData G input represented))))
        (PaperQuaternaryDecision.RuntimeSevenPrograms.executes.cost
          (quaternaryData G input represented))) ∧
      (PaperQuaternaryDecisionSource.answer (quaternaryData G input represented) = true ↔
        Tract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G))) ∧
      (PaperQuaternaryDecisionSource.answer (quaternaryData G input represented) = false ↔
        ¬Tract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G))) := by
  obtain ⟨M, hM⟩ := PaperQuaternaryDecisionSource.uniform_source
  refine ⟨M, ?_⟩
  intro s a G input represented
  exact hM (quaternaryData G input represented)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems
end
