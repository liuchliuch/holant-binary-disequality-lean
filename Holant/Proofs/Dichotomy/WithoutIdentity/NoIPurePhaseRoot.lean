import Holant.Tractable.AffinePhase.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoScalar
open Holant Holant.Tractable
local instance : IsAlgClosed AlgebraicComplex:=IsAlgClosure.isAlgClosed ℚ

def rho : AlgebraicComplex:=(IsAlgClosed.exists_pow_nat_eq imaginaryUnit (by decide : 0<4)).choose
theorem rho_four : rho^4=imaginaryUnit:=(IsAlgClosed.exists_pow_nat_eq imaginaryUnit (by decide : 0<4)).choose_spec

theorem rho_nonzero : rho≠0:=by
  intro zero
  have h:=rho_four
  rw [zero,zero_pow (by decide)] at h
  have hi:=imaginaryUnit_sq
  rw [←h] at hi
  norm_num at hi

theorem rho_eight : rho^8= -1:=by
  calc
    rho^8=(rho^4)^2:=by ring
    _= -1:=by rw [rho_four,imaginaryUnit_sq]

theorem rho_sixteen : rho^16=1:=by
  calc
    rho^16=(rho^8)^2:=by ring
    _=1:=by rw [rho_eight];norm_num

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoScalar
end
