import Holant.Proofs.Dichotomy.Main.PaperLiteralEqualitySource
import Holant.Proofs.Dichotomy.Main.PaperLiteralEqualityCriterion
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness

/-! The actual final conversion from ordinary G plus X to native G is
composed before forgetting the counted-verifier programme's length control. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEqualityHardness
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (j : Fin s)
variable (literal : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=
  ⟨2,kernelSignature Signature.equality⟩)

def target : NoIOrdinaryRaw.Target := PaperControlledHardness.target
  (PaperLiteralEqualityCriterion.inputEncoding (s:=s) (a:=a))
  (PaperLiteralEqualityCriterion.presentation G).encoding (PaperLiteralEqualityCriterion.value G)

include j literal in
theorem controlled (hard : PaperControlledHardness.Original G) : (target G).Hard :=
  NoIOrdinaryRaw.Target.Hard.compose hard (PaperLiteralEqualitySource.ordinaryToNative G j literal)

include j literal in
theorem countingHard (hard : PaperControlledHardness.Original G) : PaperLiteralEqualityCriterion.Hard G :=
  NoIOrdinaryRaw.Target.Hard.witness (controlled G j literal hard)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEqualityHardness
end
