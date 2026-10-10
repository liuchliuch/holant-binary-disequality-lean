import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneUniform
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixingResources
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralOddAnti
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Both rank-one class witnesses terminate at actual typed resources.
Even and antidiagonal obstructions are consumed by proved original-G sources. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryRankOneDispatch
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeSparseRankDescent
open NoXGeneralMixingResources
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
variable (j : Fin src.size) (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
variable (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G)
include negative square noHard in
theorem ordinary (W : OrdinaryNegativeSparseMinimalRank.PinWitness (src.H j) 1) :
    OrdinarySupply src.H := by
  rcases NoXReciprocalSelectionRankOneSupply.ordinary src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) W square with bad|anti|standard
  · exact False.elim (noHard (NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative bad))
  · obtain ⟨row,v,w,hv,hw,he⟩:=anti
    exact False.elim (noHard (NoIOrdinaryRaw.NoXGeneralOddAnti.countingHard G src row v w hv hw he negative))
  · exact Or.inl ⟨.one,standard⟩
include negative square noHard in
theorem uniform (W : OrdinaryNegativeSparseUniformMinimal.UniformPinWitness (src.H j) 1) :
    UniformSupply src.H := by
  rcases NoXReciprocalSelectionRankOneUniform.uniform src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) W square with bad|anti|standard
  · exact False.elim (noHard (NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative bad))
  · obtain ⟨row,v,w,hv,hw,he⟩:=anti
    exact False.elim (noHard (NoIOrdinaryRaw.NoXGeneralOddAnti.countingHard G src row v w hv hw he negative))
  · exact Or.inl ⟨.one,standard⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryRankOneDispatch
end
