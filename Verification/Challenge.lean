import Holant.Statements

/-! Trusted statement-only Comparator challenge. The four `sorry` bodies are
intentional holes in this reference environment. This module is never imported
by Holant, Holant.Proofs, or the solution environment. Comparator requires the
solution proofs to use only propext, Classical.choice and Quot.sound. -/
noncomputable section
namespace Holant.Theorems
open Holant.Tractable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

theorem binaryDisequality : Statements.BinaryDisequality G := by sorry
theorem literalEquality : Statements.LiteralEquality G := by sorry
theorem quaternary : Statements.Quaternary G := by sorry
theorem tractableEvaluation : Statements.TractableEvaluation G := by sorry

end Holant.Theorems
end
