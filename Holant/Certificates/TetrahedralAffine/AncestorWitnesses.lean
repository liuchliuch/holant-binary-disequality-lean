import Holant.Certificates.TetrahedralAffine.AncestorWitnessData

namespace Holant.Certificates.TetrahedralAffine
open Holant Holant.Tractable
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

/-- No source coefficient formula is assumed: all192 entries follow by expanding
the reconstructed tensors and the displayed phase/support witnesses. -/
theorem ancestor_formula (s : Orientation) :
    ancestor s = affineFormula (scale s) (supportSystem s) (phase s) := by
  fin_cases s <;> funext x <;>
    rcases h0 : x 0 with _ | _ <;> rcases h1 : x 1 with _ | _ <;>
    rcases h2 : x 2 with _ | _ <;> rcases h3 : x 3 with _ | _ <;>
    rcases h4 : x 4 with _ | _ <;> rcases h5 : x 5 with _ | _ <;>
    norm_num [ancestor,dual,cardImages,axisR,p2,Q,sigma,Signature.equality,smul_eq_mul,
      affineFormula,scale,supportSystem_holds_bool,phase_eval,sourcePhase,
      Fin.sum_univ_succ,bitValue,fourthRootPhase,ZMod.val_natCast,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,ZMod.natCast_self,imaginaryUnit_sq,imaginaryUnit_pow_three,
      h0,h1,h2,h3,h4,h5] <;>
    (try ring_nf) <;> norm_num [imaginaryUnit_sq,ZMod.val_natCast,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] <;> ring

theorem ancestor_affine (s : Orientation) : Affine (ancestor s) := by
  rw [ancestor_formula]
  exact affine_formula _ _ _

theorem scale_ne_zero (s : Orientation) : scale s ≠ 0 := by
  intro h
  have hc := congrArg (fun z : AlgebraicComplex => (z : ℂ)) h
  fin_cases s <;> norm_num [scale,Complex.ext_iff] at hc

end
end Holant.Certificates.TetrahedralAffine
