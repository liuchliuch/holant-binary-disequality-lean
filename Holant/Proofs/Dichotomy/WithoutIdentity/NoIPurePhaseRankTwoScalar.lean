import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRoot
import Holant.Proofs.Hardness.EOBinaryPlaneAffine

/-! One fixed sixteenth phase corrects the non-affine binary interaction
when support-weight differences are multiples of four and the cross-weight
increment is four modulo eight. All original coefficient scalars survive. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoScalar
open Holant Holant.Tractable
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
  (Full CommonFourth Cross SignedCross full_affine_iff)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false


theorem negative_cross (u : Signature AlgebraicComplex 2) (full : B.Full u)
    (fourth : B.CommonFourth u) (bad : ¬Affine u) :
    (u ![false,false]*u ![true,true])^2= -(u ![false,true]*u ![true,false])^2 := by
  have powers:(u ![false,false]*u ![true,true])^4=(u ![false,true]*u ![true,false])^4:=by
    simp only [mul_pow,fourth ![true,true],fourth ![false,true],fourth ![true,false]]
  have squares:((u ![false,false]*u ![true,true])^2)^2=
      ((u ![false,true]*u ![true,false])^2)^2:=by simpa only [←pow_mul] using powers
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp squares with same|negative
  · have cross:B.SignedCross u:=sq_eq_sq_iff_eq_or_eq_neg.mp same
    exact False.elim (bad ((B.full_affine_iff u full).mpr ⟨fourth,cross⟩))
  · exact negative

def twist (w : (Fin 2→Bool)→ℕ) (u : Signature AlgebraicComplex 2) : Signature AlgebraicComplex 2:=
  fun x=>rho^(w x)*u x

theorem phase_fourth (a b : ℕ) (same : a%4=b%4) : (rho^a)^4=(rho^b)^4:=by
  have commute (k : ℕ) : (rho^k)^4=(rho^4)^k:=by rw [←pow_mul,←pow_mul,Nat.mul_comm]
  rw [commute,commute,rho_four]
  exact pow_eq_pow_of_modEq same imaginaryUnit_pow_four

theorem phase_cross (a b : ℕ) (cross : a%8=(b+4)%8) : rho^(2*a)= -(rho^(2*b)):=by
  have congruence:2*a%16=(2*b+8)%16:=by omega
  have he:=pow_eq_pow_of_modEq congruence rho_sixteen
  exact he.trans (by rw [pow_add,rho_eight,mul_neg_one])

theorem cross_factor (w : (Fin 2→Bool)→ℕ) (u : Signature AlgebraicComplex 2) (x y : Fin 2→Bool) :
    (twist w u x*twist w u y)^2=rho^(2*(w x+w y))*(u x*u y)^2 := by
  calc
    _=((rho^(w x)*rho^(w y))*(u x*u y))^2:=by unfold twist;ring
    _=(rho^(w x+w y))^2*(u x*u y)^2:=by rw [←pow_add,mul_pow]
    _=_:=by rw [←pow_mul,Nat.mul_comm (w x+w y) 2]

theorem affine (w : (Fin 2→Bool)→ℕ) (u : Signature AlgebraicComplex 2)
    (full : B.Full u) (fourth : B.CommonFourth u) (bad : ¬Affine u)
    (same : ∀x,w x%4=w ![false,false]%4)
    (cross : (w ![false,false]+w ![true,true])%8=
      (w ![false,true]+w ![true,false]+4)%8) : Affine (twist w u) := by
  have full':B.Full (twist w u):=fun x=>mul_ne_zero (pow_ne_zero _ rho_nonzero) (full x)
  apply (B.full_affine_iff _ full').mpr
  constructor
  · intro x
    simp only [twist,mul_pow,phase_fourth _ _ (same x),fourth x]
  · apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [cross_factor,cross_factor,phase_cross _ _ cross,negative_cross u full fourth bad]
    ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoScalar
end
