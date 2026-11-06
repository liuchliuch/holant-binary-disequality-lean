import Holant.Statements
import Holant.Tractable.ReducedEdgeBridge
import Holant.Tractable.QuaternaryAnchor
import Holant.Proofs.Dichotomy.Main.PaperMainTheorems
import Holant.Proofs.Algorithms.ReturnedLPTractSourceV2

/-! Proofs of the current public specifications. The algebraic bridges preserve
both directions of the criteria before the retained dichotomies are applied.
Comparator checks the current public names in a separate reference environment. -/
noncomputable section
namespace Holant.Theorems
open Holant.Tractable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

/-- Theorems 1.1/F.1.1, with the direct original-coordinate reduced criterion. -/
theorem binaryDisequality : Statements.BinaryDisequality G := by
  have h := LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems.binaryDisequality G
  have bridge := tractX_edge_bridge (Statements.family G)
  exact ⟨fun criterion => h.1 (bridge.mp criterion),
    fun criterion => h.2 (fun old => criterion (bridge.mpr old))⟩

/-- Theorem F.5.2, equality-accessible K-Holant on the original family. -/
theorem equalityAccessible : Statements.EqualityAccessible G := by
  intro identity
  exact LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems.literalEquality G identity

/-- Theorems 1.2/F.1.2, with the native disequality-edge four-case criterion. -/
theorem quaternary : Statements.Quaternary G := by
  intro q member even endpoint prime
  have h := LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems.quaternary
    G q member even endpoint prime
  have bridge : Tract (familyAction sourceKBasis (Statements.family G)) ↔
      ReTractX (Statements.family G) :=
    (tract_iff_tractX_of_quaternary_endpoints member even endpoint).trans
      (reTractX_iff_reTract_K (Statements.family G)).symm
  exact ⟨fun criterion => h.1 (bridge.mpr criterion),
    fun criterion => h.2 (fun old => criterion (bridge.mp old))⟩

/-- Theorem F.3.3, polynomial-time evaluation under all seven cases. -/
theorem tractableEvaluation : Statements.TractableEvaluation G := by
  intro criterion
  exact LocalDrafts.MainChain.ReturnedLPTractSourceV2.inFP G criterion

/-- Compatibility name for the former public equality theorem (old Theorem 1.2). -/
theorem literalEquality : Statements.LiteralEquality G := equalityAccessible G

end Holant.Theorems
end
