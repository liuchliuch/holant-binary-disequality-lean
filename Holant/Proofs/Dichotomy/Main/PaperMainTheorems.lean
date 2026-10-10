import Holant.Proofs.Dichotomy.Main.PaperMainTheoremsDecision
import Holant.Proofs.Dichotomy.Main.PaperQuaternary


noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.EightVertex.ProductAnchor
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- Manuscript Theorem 1.1. The ordinary original target is Holant(F,X). -/
theorem binaryDisequality :
    (TractX (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G ∪
        {(⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)})) →
      InFP (OriginalForestSource.inputEncoding (s := s) (arity := a))
        (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)) ∧
    (¬TractX (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G ∪
        {(⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)})) →
      NoXWeightedAntiResourcesOriginal.Hard G) :=
  PaperBinaryDisequality.dichotomy G

/-- Manuscript Theorem 1.2. Literal I is a member of the original native family. -/
theorem literalEquality
    (identity : (⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) ∈
      PaperLiteralEqualityCriterion.family G) :
    (TractX (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G)) →
      InFP (PaperLiteralEqualityCriterion.inputEncoding (s := s) (a := a))
        (PaperLiteralEqualityCriterion.presentation G).encoding (PaperLiteralEqualityCriterion.value G)) ∧
    (¬TractX (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G)) →
      PaperLiteralEqualityCriterion.Hard G) :=
  PaperLiteralEquality.dichotomy_of_member G identity

/-- Manuscript Theorem 1.3, with the endpoint product written exactly as stated.
There is no literal-equality membership assumption or adjoined signature. -/
theorem quaternary (q : Signature AlgebraicComplex 4)
    (member : (⟨4, q⟩ : AnySignature AlgebraicComplex) ∈ PaperLiteralEqualityCriterion.family G)
    (even : ∀ x, Holant.weight x % 2 = 1 → q x = 0)
    (endpoint : q (fun _ => false) * q (fun _ => true) ≠ 0)
    (prime : Holant.Certificates.EqualityQuaternary.TensorPrime q) :
    (Tract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G)) →
      InFP (PaperLiteralEqualityCriterion.inputEncoding (s := s) (a := a))
        (PaperLiteralEqualityCriterion.presentation G).encoding (PaperLiteralEqualityCriterion.value G)) ∧
    (¬Tract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G)) →
      PaperLiteralEqualityCriterion.Hard G) := by
  have endpoints := (mul_ne_zero_iff.mp endpoint)
  exact PaperQuaternary.dichotomy_of_member G q member
    ⟨endpoints.1, endpoints.2, even⟩ prime


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems
end
