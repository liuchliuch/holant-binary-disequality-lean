import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLegalAffine
import Holant.Proofs.Hardness.GeneralEONegativeSupportClosure
import Holant.ReedMuller.AffinePatching.AffineSupport

/-! Four literal copies are a charge-zero recipe. Thus legal recipe closure
already forces affine fourth powers and ternary-closed original support. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureLegalSupport
open Holant Holant.Tractable
open scoped BigOperators
namespace L
export NoIPurePhaseLegalAffine (LegalAffine)
end L
namespace R
export NoIPurePhaseRecipeFactor (Port word incidence total)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {n : ℕ}

def identityPorts : Fin 4 → Fin n → R.Port n := fun _ j => .inr (j,false)

theorem fourth (f : Signature AlgebraicComplex n) (legal : L.LegalAffine f) :
    Affine (fun z => f z ^ 4) := by
  have count (j : Fin n) : R.total (identityPorts (n:=n)) j % 4 = 0 := by
    classical
    simp [R.total,R.incidence,identityPorts]
  have h := legal n 4 identityPorts count
  have words (i : Fin 4) (z : Fin n → Bool) : R.word (identityPorts i) z = z := by
    funext j
    simp [R.word,identityPorts]
  convert h using 1
  funext z
  simp only [Fin.prod_univ_four,words]
  ring

theorem closed (f : Signature AlgebraicComplex n) (legal : L.LegalAffine f) :
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport.Closed f := by
  intro a b c ha hb hc
  have h := Holant.ReedMuller.AffinePatching.affine_support_ternary
    (fun z => f z ^ 4) (fourth f legal) a b c
    (pow_ne_zero _ ha) (pow_ne_zero _ hb) (pow_ne_zero _ hc)
  change f (Holant.Tractable.AffinePhase.xor (Holant.Tractable.AffinePhase.xor a b) c) ≠ 0
  exact (pow_ne_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureLegalSupport
end
