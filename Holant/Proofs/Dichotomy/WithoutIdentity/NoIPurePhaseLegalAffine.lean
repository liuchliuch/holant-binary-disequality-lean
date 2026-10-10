import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRecipeFactor

/-! The concrete signed-recipe closure used by the phase classifier.
Every factor is a literal substitution into the same original coefficient
row. A separate original-labelled tensor/compression theorem supplies this
property from the no-hard hypothesis; it is not a new hardness backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseLegalAffine
open Holant Holant.Tractable
open NoIPurePhaseRecipeFactor (Port word incidence total)
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {n : ℕ}

def LegalAffine (f : Signature AlgebraicComplex n) : Prop :=
  ∀m k : ℕ,∀ps : Fin k→Fin n→Port m,
    (∀j,total ps j%4=0)→Affine (fun z=>∏i : Fin k,f (word (ps i) z))

theorem single (f : Signature AlgebraicComplex n) (legal : LegalAffine f)
    {m : ℕ} (p : Fin n→Port m) (zero : ∀j,incidence p j%4=0) :
    Affine (fun z=>f (word p z)) := by
  have h:=legal m 1 (fun _=>p) (fun j=>by simpa [total,Fin.sum_univ_one] using zero j)
  simpa only [Fin.prod_univ_one] using h

theorem single_corrected (f : Signature AlgebraicComplex n) (legal : LegalAffine f)
    (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1)
    {m : ℕ} (p : Fin n→Port m) (zero : ∀j,incidence p j%4=0) :
    Affine (fun z=>r^(weight (word p z))*f (word p z)) := by
  have good:=NoIPurePhaseRecipeFactor.affine (fun _ : Fin 1=>p) r rn root
    (fun j=>by simpa [total,Fin.sum_univ_one] using zero j)
  have h:=good.mul (single f legal p zero)
  simpa only [NoIPurePhaseRecipeFactor.factor,Fin.prod_univ_one] using h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseLegalAffine
end
