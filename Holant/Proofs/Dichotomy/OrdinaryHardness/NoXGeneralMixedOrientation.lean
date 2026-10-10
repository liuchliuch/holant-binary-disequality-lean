import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralParityBool
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalEvenCharacterPhase

/-! Every odd total signed bundle has exactly one odd orientation. Selecting
it uses actual separate counts and leaves the opposite private group even. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralMixedOrientation
open Holant
open OrdinaryNegativeSignedPortsCore (Port)
namespace P
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
namespace B
export NoXGeneralParityBool (even_iff odd_iff)
end B
set_option maxHeartbeats 700000
set_option Elab.async false
variable {n m : ℕ} (ps : Fin n→Port m)

def sign (j : Fin m) : Bool := Nat.bodd (P.signedCount ps j true)

variable (total : ∀j,Odd (P.bundleSize ps j))
include total in
theorem total_parity (j : Fin m) :
    (Nat.bodd (P.signedCount ps j true) ^^ Nat.bodd (P.signedCount ps j false))=true := by
  have h:=total j
  rw [B.odd_iff,←NoXLocalEvenCharacterPhase.totalCount ps j,Fintype.sum_bool,Nat.bodd_add] at h
  exact h

include total in
theorem odd (j : Fin m) : Odd (P.signedCount ps j (sign ps j)) := by
  have h:=total_parity ps total j
  rw [B.odd_iff]
  cases hp : Nat.bodd (P.signedCount ps j false) <;>
    cases hn : Nat.bodd (P.signedCount ps j true) <;> simp_all [sign]

include total in
theorem even (j : Fin m) : Even (P.signedCount ps j (!(sign ps j))) := by
  have h:=total_parity ps total j
  rw [B.even_iff]
  cases hp : Nat.bodd (P.signedCount ps j false) <;>
    cases hn : Nat.bodd (P.signedCount ps j true) <;> simp_all [sign]

include total in
theorem exists_orientation : ∃sign : Fin m→Bool,
    (∀q,Odd (P.signedCount ps q (sign q))) ∧ (∀q,Even (P.signedCount ps q (!(sign q)))) :=
  ⟨sign ps,odd ps total,even ps total⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralMixedOrientation
end
