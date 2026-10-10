import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeCancellationField

/-! A genuinely labelled native-X cancellation output supplies counting
hardness for its entire original finite source, without a literal-I premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeCancellationActual
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace S
export NativeAntiTargetSource (Output base)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)
variable (N : S.Output H 4) (applicable : EightVertexCancellationLocal.Applicable N.network.denote)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding count ((S.base H F).evaluate F) :=
  Programme.compose (PaperTerminalBridgeCancellationField.source F N.network.denote applicable w)
    (PaperTerminalBridgeMacroAccess.source H F N)

include N applicable in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding ((S.base H F).evaluate F) := by
  intro α ea count w
  exact ⟨(source H F N applicable w).reduction⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeCancellationActual
end
