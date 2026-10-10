import Holant.Certificates.TetrahedralOrientation.Data

/-! Reusable exact raw-card coefficients, proved from Frobenius reconstruction.
These prevent expanding the ancestor separately at every rank-certificate entry. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def rawCardNumerator (s : Orientation) (x : Fin 4 → Bool) : ℂ :=
  match x 0,x 1,x 2,x 3 with
  | false,false,false,false => ![0,-Complex.I,-Complex.I] s
  | false,false,false,true => ![1-Complex.I,-1,Complex.I] s
  | false,false,true,false => ![0,-Complex.I,-1] s
  | false,false,true,true => ![1-Complex.I,1,1] s
  | false,true,false,false => ![0,-Complex.I,-1] s
  | false,true,false,true => ![-1-Complex.I,-1,-1] s
  | false,true,true,false => ![0,Complex.I,-Complex.I] s
  | false,true,true,true => ![-1-Complex.I,-1,-Complex.I] s
  | true,false,false,false => ![1-Complex.I,1,-Complex.I] s
  | true,false,false,true => ![0,-Complex.I,Complex.I] s
  | true,false,true,false => ![-1+Complex.I,-1,-1] s
  | true,false,true,true => ![0,-Complex.I,1] s
  | true,true,false,false => ![1+Complex.I,1,1] s
  | true,true,false,true => ![0,-Complex.I,1] s
  | true,true,true,false => ![-1-Complex.I,1,Complex.I] s
  | true,true,true,true => ![0,Complex.I,Complex.I] s

theorem card_value (s : Orientation) (x : Fin 4 → Bool) :
    card s x = rawCardNumerator s x / 4 := by
  fin_cases s <;>
    rcases h0 : x 0 with _ | _ <;> rcases h1 : x 1 with _ | _ <;>
    rcases h2 : x 2 with _ | _ <;> rcases h3 : x 3 with _ | _ <;>
    norm_num [rawCardNumerator,card_apply,ancestor,Fin.sum_univ_succ,
      dual,cardImages,sigma,axisR,C,P2,Q0,Q1,Q2,Q3,Signature.equality,
      h0,h1,h2,h3,smul_eq_mul] <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

end
end Holant.Certificates.TetrahedralOrientation
