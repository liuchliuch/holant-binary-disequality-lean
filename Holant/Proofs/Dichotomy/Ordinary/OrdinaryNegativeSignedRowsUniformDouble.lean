import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniformOdd

/-! Double uniform input twists contribute an invertible Affine gauge for
any signed-row product. Together with odd-incidence transport this recovers
the actual A-type resource from the uniform-bad alpha-type classification. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsUniformDouble
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore
open scoped BigOperators
namespace G
export OrdinaryNegativeSignedRowsUniform (count gauge gauge_affine gauge_ne_zero product portFamily uniform_value)
end G
namespace U
export OrdinaryNegativeAffineRankOne (uniform)
export OrdinaryNegativeAffineSquareReciprocal (affine_inverse)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {m : ℕ} {A : Type*} [Fintype A] (p : A→Port m)

theorem gauge_square_affine : Affine (fun z=>G.gauge p z^2) := by
  let doubled : Bool×A→Port m := fun v=>p v.2
  have even : ∀j,Even (G.count doubled j) := by
    intro j
    change Even (∑v : Bool×A,OrdinaryNegativeSignedRowsUniform.incidence (p v.2) j)
    rw [Fintype.sum_prod_type,Fintype.sum_bool]
    exact ⟨_,rfl⟩
  have ha := G.gauge_affine doubled even
  convert ha using 1
  funext z
  simp [G.gauge,doubled,Fintype.prod_prod_type,Fintype.prod_bool,pow_two]

variable {r : ℕ} {n : Fin r→ℕ}
variable (f : (i : Fin r)→Signature AlgebraicComplex (n i))
variable (ports : (i : Fin r)→Fin (n i)→Port m)

theorem double_value (z : Fin m→Bool) :
    G.product (fun i=>U.uniform (U.uniform (f i))) ports z=
      G.gauge (G.portFamily ports) z^2*G.product f ports z := by
  rw [G.uniform_value,G.uniform_value]
  ring

theorem double_affine_iff :
    Affine (G.product (fun i=>U.uniform (U.uniform (f i))) ports) ↔ Affine (G.product f ports) := by
  have ha := gauge_square_affine (G.portFamily ports)
  have hn (z : Fin m→Bool) : G.gauge (G.portFamily ports) z^2≠0 :=
    pow_ne_zero 2 (G.gauge_ne_zero _ z)
  have he : G.product (fun i=>U.uniform (U.uniform (f i))) ports=
      (fun z=>G.gauge (G.portFamily ports) z^2*G.product f ports z) := funext (double_value f ports)
  rw [he]
  constructor
  · intro h
    convert (U.affine_inverse _ ha).mul h using 1
    funext z
    rw [←mul_assoc,inv_mul_cancel₀ (hn z),one_mul]
  · intro h
    exact ha.mul h

theorem odd_double_affine_iff
    (odd : ∀j,Odd (∑i,OrdinaryNegativeSignedPortsIncidence.bundleSize (ports i) j)) :
    Affine (U.uniform (G.product (fun i=>U.uniform (f i)) ports)) ↔ Affine (G.product f ports) :=
  (OrdinaryNegativeSignedRowsUniformOdd.affine_iff (fun i=>U.uniform (f i)) ports odd).symm.trans
    (double_affine_iff f ports)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsUniformDouble
end
