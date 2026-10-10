import Holant.Statements
import Holant.Proofs.Dichotomy.Main.PaperMainTheorems
import Holant.Proofs.Algorithms.ReturnedLPTractSourceV2

/-! Proofs of the independently stated public specifications. The Comparator
challenge uses the same public theorem names in a separate Lean environment. -/
noncomputable section
namespace Holant.Theorems
open Holant.Tractable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

/-- Manuscript Theorem 1.1, complexity dichotomy. -/
theorem binaryDisequality : Statements.BinaryDisequality G := by
  exact LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems.binaryDisequality G

/-- Manuscript Theorem 1.2, complexity dichotomy. -/
theorem literalEquality : Statements.LiteralEquality G := by
  intro identity
  exact LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems.literalEquality G identity

/-- Manuscript Theorem 1.3, complexity dichotomy. -/
theorem quaternary : Statements.Quaternary G := by
  intro q member even endpoint prime
  exact LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems.quaternary
    G q member even endpoint prime

/-- Manuscript Theorem 2.19, polynomial-time evaluation. -/
theorem tractableEvaluation : Statements.TractableEvaluation G := by
  intro criterion
  exact LocalDrafts.MainChain.ReturnedLPTractSourceV2.inFP G criterion

end Holant.Theorems
end
