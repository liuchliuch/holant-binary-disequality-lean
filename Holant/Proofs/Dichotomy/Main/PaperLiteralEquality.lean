import Holant.Proofs.Dichotomy.Main.PaperLiteralEqualityHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineComplete

/-! Exact supplied-equality theorem for the original finite native-X family.
The criterion is TractX(KG), without a duplicate adjoined signature. Both
outcomes use OriginalFamily.value G nativeEdges and its generated answer field.
The negative route retains actual source control through the final wire and
literal-label conversion; no hardness transport callback is an input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEquality
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
abbrev family:=PaperLiteralEqualityCriterion.family G
abbrev Criterion:=PaperLiteralEqualityCriterion.Criterion G
abbrev Hard:=PaperLiteralEqualityCriterion.Hard G
abbrev inputEncoding:=PaperLiteralEqualityCriterion.inputEncoding (s:=s) (a:=a)
abbrev presentation:=PaperLiteralEqualityCriterion.presentation G
abbrev value:=PaperLiteralEqualityCriterion.value G

variable (j : Fin s)
variable (literal : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=
  ⟨2,kernelSignature Signature.equality⟩)
include j literal in
theorem criterion_or_controlledHard : Criterion G ∨ (PaperLiteralEqualityHardness.target G).Hard := by
  rcases PaperControlled.EngineComplete.original_current_classified G with tract|hard
  · exact Or.inl (by
      have old:=GlobalCloseCompletionOriginalCriterion.of_current G tract
      rwa [PaperLiteralEqualityCriterion.retained_eq G j literal] at old)
  · exact Or.inr (PaperLiteralEqualityHardness.controlled G j literal hard)

theorem positive (criterion : Criterion G) :
    InFP (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (value G) :=
  PaperLiteralEqualityCriterion.positive G criterion

include j literal in
theorem controlledNegative (negative : ¬Criterion G) : (PaperLiteralEqualityHardness.target G).Hard :=
  (criterion_or_controlledHard G j literal).resolve_left negative

include j literal in
theorem negative (criterion : ¬Criterion G) : Hard G :=
  NoIOrdinaryRaw.Target.Hard.witness (controlledNegative G j literal criterion)

include j literal in
theorem dichotomy :
    (Criterion G→InFP (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (value G)) ∧
    (¬Criterion G→Hard G) :=⟨positive G,negative G j literal⟩

theorem dichotomy_of_member (identity : (⟨2,kernelSignature Signature.equality⟩ :
    AnySignature AlgebraicComplex)∈family G) :
    (Criterion G→InFP (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (value G)) ∧
    (¬Criterion G→Hard G) := by
  obtain ⟨j,literal⟩:=identity
  exact dichotomy G j literal


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEquality
end
