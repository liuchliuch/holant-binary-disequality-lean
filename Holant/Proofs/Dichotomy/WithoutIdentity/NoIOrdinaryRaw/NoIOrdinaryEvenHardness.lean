import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryBinaryHardness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXNonproduct
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralBinarySupply
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralFullBinarySupply
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! A genuine non-Affine even resource closes any obstructed ordinary
Eq4/two-pin source, with no supplied trace-zero or sign signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))

include negative in
theorem countingHard (bad : B.EvenBad src.H) : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_contra noHard
  obtain ⟨m,first,nonaffine⟩:=bad
  let second : B.Block (s:=src.size) (b:=src.b) (NoIOrdinaryRaw.NoXNonproduct.arity G src negative):=
    ⟨0,NoIOrdinaryRaw.NoXNonproduct.blocks G src negative,NoIOrdinaryRaw.NoXNonproduct.balanced G src negative⟩
  obtain ⟨row,badA,badP⟩:=NoIOrdinaryRaw.NoXGeneralBinarySupply.exists_binary G src first second nonaffine
    (NoIOrdinaryRaw.NoXNonproduct.row_nonproduct G src negative) noHard
  exact noHard (NoIOrdinaryRaw.NoIOrdinaryBinaryHardness.countingHard G src row
    (NoIOrdinaryRaw.NoXGeneralFullBinarySupply.full G src noHard row badP) badA badP
    ((NoIOrdinaryRaw.GenericOrdinarySource.rejected_iff G src).mpr negative))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
end
