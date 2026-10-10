import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureClosedUniformMinimal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLegalAffine
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureUniformFour

/-! Any actual signed rank-one support encoding has one legal column when
support weights agree modulo four. All root-sixteen twists are then Affine. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankOneCore
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport
open NoIPurePhaseRecipeFactor (Port word incidence)
open NoIPurePhaseLegalAffine (LegalAffine)
open scoped BigOperators
namespace U
export NoIPureClosedUniformMinimal (twist twistChart)
end U
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {n : ℕ} {f : Signature AlgebraicComplex n}
def one (D : SystematicSupport f 1) (i : Fin n) : Port 1 :=
  let a:=D.encode (fun _=>false) i
  let b:=D.encode (fun _=>true) i
  if a=b then .inl a else .inr (0,a)

theorem one_value (D : SystematicSupport f 1) (z : Fin 1→Bool) : word (one D) z=D.encode z := by
  have hz : z=(fun _=>z 0) := by funext j;fin_cases j;rfl
  rw [hz]
  funext i
  cases h0:z 0 <;> cases ha:D.encode (fun _=>false) i <;> cases hb:D.encode (fun _=>true) i <;>
    simp [one,word,ha,hb]

variable (D : SystematicSupport f 1) (p : Fin n→Port 1)
variable (encoding : ∀z,word p z=D.encode z)

include encoding in
theorem column_zero (uniform : NoIPureChargeTwoFamily.UniformFour f) :
    ∀j,incidence p j%4=0 := by
  have same:=uniform (D.encode (fun _=>true)) (D.encode (fun _=>false))
    (D.supported _) (D.supported _)
  have difference : (weight (D.encode (fun _=>true)) : ℤ)-
      weight (D.encode (fun _=>false))=incidence p (0 : Fin 1) := by
    simpa [encoding,Fin.sum_univ_one] using
      NoIPurePhaseRecipeFactor.weight_difference p (fun _=>true)
  have result : incidence p (0 : Fin 1)%4=0 := by omega
  intro j
  have hj : j=0:=Subsingleton.elim _ _
  simpa only [hj] using result

include encoding in
theorem affine (uniform : NoIPureChargeTwoFamily.UniformFour f) (legal : LegalAffine f)
    (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1) : Affine (U.twist r f) := by
  let E:=U.twistChart r rn D
  have reduced : Affine E.reduced := by
    change Affine (fun z=>r^(weight (D.encode z))*f (D.encode z))
    simpa only [encoding] using NoIPurePhaseLegalAffine.single_corrected f legal r rn root
      p (column_zero D p encoding uniform)
  obtain ⟨S,hS⟩:=NoIPureClosedMinimal.support_system f
    (NoIPureClosedMinimal.chart_closed D) (NoIPureClosedMinimal.chart_nonzero D)
  apply E.affine_of_reduced S ?_ reduced
  intro x
  change S.Holds x↔r^(weight x)*f x≠0
  simpa only [mul_ne_zero_iff,and_iff_right (pow_ne_zero _ rn)] using hS x


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankOneCore
end
