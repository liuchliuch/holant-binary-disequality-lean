import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalSelectionRankOneDistance
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalRankOneWeighted
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXGeneralOddAnti
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryEvenHardness
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! A LocalAffine but non-Affine rank-one pin minor has even physical
distance. Its two separate incidence counts are therefore both even or
both odd, yielding an actual even bad block or an actual odd anti resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryRankOneLocalHardness
open Holant Holant.Tractable
namespace P
export NoXReciprocalSelectionRankOne (ports)
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSparseMinimalRank (PinWitness row)
end P
namespace A
export OrdinaryNegativeAffineRankOne.SystematicSupport (left right)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : NoIOrdinaryRaw.Target)
variable (src : NoIOrdinaryRaw.GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (NoIOrdinaryRaw.GenericOrdinarySource.family G src)))
variable (j : Fin src.size) (W : P.PinWitness (src.H j) 1)
variable (square : Affine (fun x=>(src.H j x : AlgebraicComplex)^2))
variable (localGood : LocalAffine (P.row (src.H j) W.pins))

include negative square localGood in
theorem countingHard : NoIOrdinaryRaw.NoXWeightedAntiResourcesOriginal.Hard G := by
  have even:=(NoXLocalRankOneWeighted.local_iff_even_sign W.chart (W.square square)).mp localGood |>.1
  rw [NoXReciprocalSelectionRankOneDistance.counts] at even
  let x:=A.left W.chart
  let y:=A.right W.chart
  rcases Nat.even_or_odd (P.signedCount (P.ports x y) 0 false) with ep|op
  · have en : Even (P.signedCount (P.ports x y) 0 true):=by
      have h:=(Nat.even_add.mp even)
      exact h.mp ep
    apply NoIOrdinaryRaw.NoIOrdinaryEvenHardness.countingHard G src negative
    apply NoXReciprocalSelectionRankOneParity.evenBad src.H j (src.p false) (src.p true)
      (src.hp false) (src.hp true) W square
    intro q bit
    have hq:q=0:=Fin.eq_zero q
    subst q
    cases bit
    · exact ep
    · exact en
  · have on : Odd (P.signedCount (P.ports x y) 0 true):=by
      rcases Nat.even_or_odd (P.signedCount (P.ports x y) 0 true) with en|on
      · have ep:=(Nat.even_add.mp even).mpr en
        exact False.elim (Nat.not_even_iff_odd.mpr op ep)
      · exact on
    obtain ⟨R,v,w,hv,hw,eqn⟩:=NoXReciprocalSelectionRankOneMinimal.exists_anti src.H j
      (src.p false) (src.p true) (src.hp false) (src.hp true) W (by
        intro q bit
        have hq:q=0:=Fin.eq_zero q
        subst q
        cases bit
        · exact op
        · exact on)
    exact NoIOrdinaryRaw.NoXGeneralOddAnti.countingHard G src R v w hv hw eqn negative

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.NoIOrdinaryRankOneLocalHardness
end
