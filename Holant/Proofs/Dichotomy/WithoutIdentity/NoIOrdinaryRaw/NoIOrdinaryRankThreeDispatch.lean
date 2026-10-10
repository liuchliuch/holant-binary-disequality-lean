import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralSevenDispatch
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeMixedSupport
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeRegularSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeUniformRegularSupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeOppositeSupply
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! Complete rank-three actual ordinary and uniform supplies. All finite
count repairs, shifted seven-port cases and opposite resources are selected
internally and remain over the unchanged original source dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryRankThreeDispatch
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeSparseRankDescent NoXGeneralMixingResources
namespace A
export NoXReciprocalRankThreeMixedSource (resource alpha)
export NoXReciprocalRankThreeMixedSupport (ordinary)
end A
namespace U
export NoXReciprocalRankThreeUniformMixedSource (resource affine)
export NoXReciprocalRankThreeMixedSupport (uniform)
end U
namespace P
export NoXGeneralMixedOrientation (sign)
export OrdinaryNegativeSparseRankThreePorts (port)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
variable (j : Fin src.size) (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
variable (noHard : ¬NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G)
include negative square noHard in
theorem ordinary (W : OrdinaryNegativeSparseMinimalRank.PinWitness (src.H j) 3)
    (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (minor W.chart S z)) :
    OrdinarySupply src.H := by
  rcases NoXReciprocalRankThreeRegularSupply.ordinary src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) W minimal square with bad|total|both
  · exact False.elim (noHard (NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative bad))
  · rcases NoIOrdinaryRaw.NoXGeneralSevenDispatch.ordinary G src
      (A.resource src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total)
      (P.sign (P.port W.chart))
      (A.ordinary src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total) negative
      (A.alpha src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total square minimal)
      with hard|result
    · exact False.elim (noHard hard)
    · exact Or.inl ⟨.seven,result⟩
  · exact Or.inr ⟨.seven,⟨NoXReciprocalRankThreeOppositeSupply.ordinary src.H j (src.p false) (src.p true)
      (src.hp false) (src.hp true) W both square minimal⟩⟩
include negative square noHard in
theorem uniform (W : OrdinaryNegativeSparseUniformMinimal.UniformPinWitness (src.H j) 3)
    (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,
      Affine (OrdinaryNegativeAffineRankOne.uniform (minor W.chart S z))) :
    UniformSupply src.H := by
  rcases NoXReciprocalRankThreeUniformRegularSupply.uniform src.H j (src.p false) (src.p true)
    (src.hp false) (src.hp true) W square minimal with bad|total|both
  · exact False.elim (noHard (NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative bad))
  · rcases NoIOrdinaryRaw.NoXGeneralSevenDispatch.uniform G src
      (U.resource src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total)
      (P.sign (P.port W.chart))
      (U.uniform src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total) negative
      (U.affine src.H j (src.p false) (src.p true) (src.hp false) (src.hp true) W total square minimal)
      with hard|result
    · exact False.elim (noHard hard)
    · exact Or.inl ⟨.seven,result⟩
  · exact Or.inr ⟨.seven,⟨NoXReciprocalRankThreeOppositeSupply.uniform src.H j (src.p false) (src.p true)
      (src.hp false) (src.hp true) W both square minimal⟩⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryRankThreeDispatch
end
