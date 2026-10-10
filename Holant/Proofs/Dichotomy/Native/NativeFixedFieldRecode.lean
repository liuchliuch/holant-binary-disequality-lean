import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeMacroAccess

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeFixedFieldRecode
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s d e : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K d) (E : FixedField K e)

theorem value (q : ExactSignatureTables.Input s 1 a) :
    (NativeAntiTargetSource.base H F).evaluate F q=(NativeAntiTargetSource.base H E).evaluate E q := by
  rw [PaperTerminalBridgeMacroAccess.value,PaperTerminalBridgeMacroAccess.value]

def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) E.encoding
    ((NativeAntiTargetSource.base H F).evaluate F) ((NativeAntiTargetSource.base H E).evaluate E) :=
  controlledOneQueryOfEq (identityComputes _) (FieldCodec.computes E F (LinearMap.id))
    ((NativeAntiTargetSource.base H E).outputBound E) ((NativeAntiTargetSource.base H F).evaluate F)
    (fun q=>value H F E q)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeFixedFieldRecode
end
