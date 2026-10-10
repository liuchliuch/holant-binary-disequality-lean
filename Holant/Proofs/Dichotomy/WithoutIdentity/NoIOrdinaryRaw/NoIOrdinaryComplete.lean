import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinarySupplierSelection
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryRankOneDispatch
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryRankTwoDispatch
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryRankThreeDispatch
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryLocalMixingOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Universal ordinary Eq4/two-pin classification without a supplied sign
or trace-zero binary. Every class witness, actual even resource, finite-power
Gram, field codec, and counted-verifier programme is derived internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryComplete
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open NoXGeneralMixingResources
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
variable (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G)
include negative noHard in
theorem ordinary : OrdinarySupply src.H := by
  obtain ⟨j,r,lower,upper,W,minimal⟩:=NoIOrdinaryRaw.NoIOrdinarySupplierSelection.ordinary G src negative noHard
  have square:=NoIOrdinaryRaw.NoIOrdinarySupplierSelection.square G src negative noHard j
  have cases_r : r=1 ∨ r=2 ∨ r=3:=by omega
  rcases cases_r with rfl|rfl|rfl
  · exact NoIOrdinaryRaw.NoIOrdinaryRankOneDispatch.ordinary G src negative j square noHard W
  · exact NoIOrdinaryRaw.NoIOrdinaryRankTwoDispatch.ordinary G src negative j square noHard W minimal
  · exact NoIOrdinaryRaw.NoIOrdinaryRankThreeDispatch.ordinary G src negative j square noHard W minimal
include negative noHard in
theorem uniform : UniformSupply src.H := by
  obtain ⟨j,r,lower,upper,W,minimal⟩:=NoIOrdinaryRaw.NoIOrdinarySupplierSelection.uniform G src negative noHard
  have square:=NoIOrdinaryRaw.NoIOrdinarySupplierSelection.square G src negative noHard j
  have cases_r : r=1 ∨ r=2 ∨ r=3:=by omega
  rcases cases_r with rfl|rfl|rfl
  · exact NoIOrdinaryRaw.NoIOrdinaryRankOneDispatch.uniform G src negative j square noHard W
  · exact NoIOrdinaryRaw.NoIOrdinaryRankTwoDispatch.uniform G src negative j square noHard W minimal
  · exact NoIOrdinaryRaw.NoIOrdinaryRankThreeDispatch.uniform G src negative j square noHard W minimal
include negative in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_contra noHard
  exact noHard (NoIOrdinaryRaw.NoIOrdinaryLocalMixingOriginal.countingHard G src negative
    (ordinary G src negative noHard) (uniform G src negative noHard))

include src in
theorem classified : Tract (NoIOrdinaryRaw.GenericOrdinarySource.family G src) ∨ NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_cases good : Tract (NoIOrdinaryRaw.GenericOrdinarySource.family G src)
  · exact Or.inl good
  · exact Or.inr (countingHard G src ((NoIOrdinaryRaw.GenericOrdinarySource.rejected_iff G src).mp good))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryComplete
end
