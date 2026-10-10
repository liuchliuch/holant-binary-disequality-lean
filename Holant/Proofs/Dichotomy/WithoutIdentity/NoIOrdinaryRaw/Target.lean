import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.TargetCore
import Holant.Proofs.Dichotomy.General.GenericOrdinarySource
import Holant.Proofs.Counting.Hardness

/-! An explicit oracle destination. No extra binary, signature family,
classification result, or successful hardness callback is carried here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2


theorem Target.Hard.compose {S T : Target} (hard : S.Hard)
    (back : LengthControlledOracleReduction S.inputEncoding S.outputEncoding
      T.inputEncoding T.outputEncoding S.value T.value) : T.Hard := by
  intro A encoding count witness
  obtain ⟨source⟩:=hard A encoding count witness
  exact ⟨Programme.compose source back⟩

theorem Target.Hard.witness {T : Target} (hard : T.Hard) :
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard T.inputEncoding T.outputEncoding T.value := by
  intro A encoding count witness
  obtain ⟨source⟩:=hard A encoding count witness
  exact ⟨source.reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw
end
