import Holant.Proofs.Dichotomy.Closure.Engine.GlobalCloseCompletionEngineComplete
import Holant.Proofs.Dichotomy.Closure.Original.GlobalCloseCompletionOriginalCriterion

/-! Main binary-disequality theorem on the original literal Holant(F,X)
input. The criterion is exactly TractX(K(F union {I})); both implications
are unconditional, including zero/nullary original rows and one shared basis.
The uniform exact-input decision programme is packaged separately. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperBinaryDisequality
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export BinaryDisequalityTractability (retainedFamily inFP)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
abbrev Criterion:=TractX (familyAction sourceKBasis (B.retainedFamily G))
abbrev Hard:=NoXWeightedAntiResourcesOriginal.Hard G

theorem criterion_or_hard : Criterion G ∨ Hard G := by
  rcases GlobalCloseCompletionEngineComplete.original_current_classified G with tract|hard
  · exact Or.inl (GlobalCloseCompletionOriginalCriterion.of_current G tract)
  · exact Or.inr hard

theorem positive (criterion : Criterion G) :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) :=
  B.inFP G criterion

theorem negative (criterion : ¬Criterion G) : Hard G :=
  (criterion_or_hard G).resolve_left criterion

theorem dichotomy :
    (Criterion G→InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)) ∧
    (¬Criterion G→Hard G) :=⟨positive G,negative G⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperBinaryDisequality
end
