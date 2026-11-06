import Holant.Proofs.Dichotomy.Main.PaperMainTheoremsDecision
import Holant.Proofs.Recognition.RuntimeSevenDecision
import Holant.Tractable.STOC2027
import Holant.Tractable.ReducedEdgeBridge

/-! Exact algebraic-input recognition for the November 2026 STOC manuscript.
Each theorem quantifies one Turing machine before every finite family layout
and RootCode input. Execution witnesses retain the original input encoding,
output encoding and actual terminating cost; no polynomial-time recognition
bound is asserted. The quaternary criterion now has four clauses, so its
recognizer uses the same four-case machine as the equality-accessible theorem.
-/
noncomputable section
namespace Holant.Decidability
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false

/-- The binary-disequality theorem's direct ordinary-edge criterion.
The output of the existing uniform machine is transported by the proved
edge-model equivalence, with no new premise or recognition oracle. -/
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
        ReTract (PaperLiteralEqualityCriterion.family G ∪
          {(⟨2, kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)})) := by
  obtain ⟨M, hM⟩ := PaperMainTheorems.binaryDisequality_uniform
  refine ⟨M, ?_⟩
  intro s a G input represented
  obtain ⟨runs, correct⟩ := hM s a G input represented
  exact ⟨runs, correct.trans
    (tractX_edge_bridge (PaperLiteralEqualityCriterion.family G)).symm⟩

/-- The equality-accessible theorem's criterion is recognized on all exact
inputs. Literal equality is a hypothesis of its complexity classification,
not an additional input or a premise needed to recognize the four cases. -/
theorem equalityAccessible_uniform : ∃ M : BinaryCompose.Machine,
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
        ReTract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G))) :=
  PaperMainTheorems.literalEquality_uniform

/-- Compatibility spelling for the equality-accessible recognition theorem. -/
alias literalEquality_uniform := equalityAccessible_uniform

/-- One machine decides the explicit disequality-edge reduced criterion on
all original exact inputs. The endpoint and irreducibility hypotheses are
needed for the quaternary dichotomy, not for recognizing this predicate.
The old seven-clause quaternary recognizer remains available in the internal
namespace, but is not used to specify the new public criterion. -/
theorem quaternary_uniform : ∃ M : BinaryCompose.Machine,
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
        ReTractX (PaperLiteralEqualityCriterion.family G)) ∧
      (PaperLiteralEqualityDecision.answer G input represented = false ↔
        ¬ReTractX (PaperLiteralEqualityCriterion.family G)) := by
  obtain ⟨M, hM⟩ := equalityAccessible_uniform
  refine ⟨M, ?_⟩
  intro s a G input represented
  obtain ⟨runs, correct⟩ := hM s a G input represented
  have accepted := correct.trans
    (reTractX_iff_reTract_K (PaperLiteralEqualityCriterion.family G)).symm
  refine ⟨runs, accepted, ?_⟩
  have false_iff : ∀ b : Bool, b = false ↔ ¬b = true := by
    intro b; cases b <;> simp
  rw [false_iff, accepted]

export Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenDecision
  (uniform_source)
end Holant.Decidability
end
