import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned

/-! Exact elimination with a literal Z and a squared pinned unary. Equal
fourth powers in the first row cancel the 00 entry; nonzero determinant keeps
both off-diagonal entries, producing an anti or a three-support binary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralZBinaryAlgebra
open Holant
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K]

def filtered (f : Signature K 2) : Signature K 2 := fun z=>
  f ![z 0,false]*f ![z 1,false]*f ![false,false]^2-
    f ![z 0,true]*f ![z 1,true]*f ![false,true]^2

theorem values (f : Signature K 2) :
    filtered f ![false,false]=f ![false,false]^4-f ![false,true]^4 ∧
    filtered f ![false,true]=f ![false,false]^3*f ![true,false]-f ![false,true]^3*f ![true,true] ∧
    filtered f ![true,false]=f ![false,false]^3*f ![true,false]-f ![false,true]^3*f ![true,true] ∧
    filtered f ![true,true]=f ![false,false]^2*f ![true,false]^2-f ![false,true]^2*f ![true,true]^2 := by
  simp only [filtered,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem cross_nonzero (a b c d : K) (ha : a≠0) (fourth : a^4=b^4) (det : a*d≠b*c) :
    a^3*c-b^3*d≠0 := by
  intro zero
  have h : a^4*(a*d-b*c)=0 := by linear_combination -(a*b)*zero+(a*d)*fourth
  exact (mul_ne_zero (pow_ne_zero 4 ha) (sub_ne_zero.mpr det)) h

theorem anti_of_zero (f : Signature K 2) (fourth : f ![false,false]^4=f ![false,true]^4)
    (zero : filtered f ![true,true]=0) :
    filtered f=NoXWeightedAntiSigned.anti (filtered f ![false,true]) (filtered f ![false,true]) := by
  have h:=values f
  have top : filtered f ![false,false]=0 := by rw [h.1,fourth,sub_self]
  have off : filtered f ![true,false]=filtered f ![false,true] := h.2.2.1.trans h.2.1.symm
  funext x
  have hx : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> simp only [NoXWeightedAntiSigned.anti]
  · exact top
  · rfl
  · exact off
  · exact zero


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralZBinaryAlgebra
end
