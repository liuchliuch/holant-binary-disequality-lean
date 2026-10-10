import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankThreeSource

/-! The square of the same root-sixteen phase corrects every rank-three
minimal row with odd signed incidence at all seven original characters. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankThreeOdd
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open NoIPurePhaseRankThreeSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false

theorem signed_odd_fourth (d : ℤ) (odd : d%2=1) : ((R.rho^2)^d)^4= -1 := by
  have he:8*d%16=8:=by omega
  calc
    ((R.rho^2)^d)^4=R.rho^(8*d):=by
      rw [←zpow_natCast R.rho 2,←zpow_mul,←zpow_natCast,←zpow_mul]
      congr 1
      ring
    _=R.rho^(8 : ℤ):=by rw [rho_zpow_mod,he]
    _= -1:=by simpa using R.rho_eight

variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 3)
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Word 3,Affine (minor D S z))

include minimal in
theorem source (bad : ¬Affine f) (p : Fin n→P.Port 7)
    (encoding : ∀x,P.word p (C.codeSeven x)=D.encode x)
    (odd : ∀j,P.incidence p j%2=1) : Affine (twist (R.rho^2) f) := by
  apply source_general D minimal bad p encoding (R.rho^2) (R.rho^2)
    (pow_ne_zero _ R.rho_nonzero) (pow_ne_zero _ R.rho_nonzero) ?_ ?_
  · simpa only [←pow_mul] using R.rho_eight
  · intro j
    rw [div_pow,signed_odd_fourth _ (odd j)]
    have h:(R.rho^2)^4= -1:=by simpa only [←pow_mul] using R.rho_eight
    rw [h]
    norm_num

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankThreeOdd
end
