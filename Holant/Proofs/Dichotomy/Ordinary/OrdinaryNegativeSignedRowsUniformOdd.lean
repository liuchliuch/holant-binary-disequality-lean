import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniform

/-! Odd-interface counterpart of the even uniform-twist law. A finite signed
original-row product with odd incidence at every exposed variable transforms
by the uniform octic twist, up to a proved invertible affine gauge. This is a
pointwise-product statement, never commutation through a private trace. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsUniformOdd
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeSignedPortsCore
open scoped BigOperators
namespace E
export OrdinaryNegativeSignedRowsUniform (phase phase_ne_zero axis axis_fourth count gauge scalar axisGauge
  gauge_factor gauge_ne_zero axisGauge_ne_zero affine_prod portFamily product count_family uniform_value)
end E
namespace R
export OrdinaryNegativeAffineRankOne (uniform)
export OrdinaryNegativeAffineSquareReciprocal (affine_inverse)
export GlobalCloseCompletionProductAncestorAffine (unary_of_equal_fourth_powers)
end R
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {m : ℕ} {A : Type*} [Fintype A] (p : A→Port m)

def uniformGauge (z : Fin m→Bool) : AlgebraicComplex := ∏j,E.phase (z j)

theorem uniformGauge_ne_zero (z : Fin m→Bool) : uniformGauge z≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact E.phase_ne_zero _

theorem uniform_apply (f : Signature AlgebraicComplex m) (z : Fin m→Bool) :
    R.uniform f z=uniformGauge z*f z := by
  simp only [R.uniform,localTwist_apply,Bool.true_and,uniformGauge,E.phase]

theorem axis_fourth (j : Fin m) (ho : Odd (E.count p j)) :
    E.axisGauge p j false^4= -(E.axisGauge p j true^4) := by
  simp only [E.axisGauge,←Finset.prod_pow,E.axis_fourth,Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  change (-1 : AlgebraicComplex)^E.count p j*(∏i,E.axis (p i) j true^4)=_
  rw [ho.neg_one_pow]
  ring

def axisCorrected (j : Fin m) (b : Bool) : AlgebraicComplex := E.axisGauge p j b/E.phase b

theorem axisCorrected_ne_zero (j : Fin m) (b : Bool) : axisCorrected p j b≠0 :=
  div_ne_zero (E.axisGauge_ne_zero p j b) (E.phase_ne_zero b)

theorem axisCorrected_fourth (j : Fin m) (ho : Odd (E.count p j)) :
    axisCorrected p j false^4=axisCorrected p j true^4 := by
  simp only [axisCorrected,div_pow,E.phase,Bool.false_eq_true,ite_false,ite_true,
    div_one,zetaEight_pow_four,div_neg,div_one]
  exact axis_fourth p j ho

theorem axisCorrected_affine (j : Fin m) (ho : Odd (E.count p j)) :
    Affine (fun z : Fin m→Bool=>axisCorrected p j (z j)) := by
  convert R.unary_of_equal_fourth_powers j (axisCorrected p j false) (axisCorrected p j true)
    (axisCorrected_ne_zero p j false) (axisCorrected_fourth p j ho) using 1
  funext z
  cases z j <;> rfl

def corrected (z : Fin m→Bool) : AlgebraicComplex := E.gauge p z/uniformGauge z

theorem corrected_factor (z : Fin m→Bool) :
    corrected p z=E.scalar p*∏j,axisCorrected p j (z j) := by
  rw [corrected,E.gauge_factor]
  simp only [axisCorrected,Finset.prod_div_distrib,uniformGauge]
  ring

theorem corrected_affine (ho : ∀j,Odd (E.count p j)) : Affine (corrected p) := by
  have hp := E.affine_prod Finset.univ (fun j=>fun z : Fin m→Bool=>axisCorrected p j (z j))
    (fun j _=>axisCorrected_affine p j (ho j))
  convert hp.scale (E.scalar p) using 1
  funext z
  exact corrected_factor p z

theorem corrected_ne_zero (z : Fin m→Bool) : corrected p z≠0 :=
  div_ne_zero (E.gauge_ne_zero p z) (uniformGauge_ne_zero z)

theorem corrected_value (f : Signature AlgebraicComplex m) (z : Fin m→Bool) :
    E.gauge p z*f z=corrected p z*R.uniform f z := by
  rw [corrected,uniform_apply]
  field_simp [uniformGauge_ne_zero z]

theorem gauge_affine_iff (ho : ∀j,Odd (E.count p j)) (f : Signature AlgebraicComplex m) :
    Affine (fun z=>E.gauge p z*f z) ↔ Affine (R.uniform f) := by
  have hv : (fun z=>E.gauge p z*f z)=(fun z=>corrected p z*R.uniform f z) :=
    funext (corrected_value p f)
  rw [hv]
  constructor
  · intro h
    convert (R.affine_inverse _ (corrected_affine p ho)).mul h using 1
    funext z
    rw [←mul_assoc,inv_mul_cancel₀ (corrected_ne_zero p z),one_mul]
  · intro h
    exact (corrected_affine p ho).mul h

section Rows
variable {r : ℕ} {n : Fin r→ℕ}
variable (f : (i : Fin r)→Signature AlgebraicComplex (n i))
variable (ports : (i : Fin r)→Fin (n i)→Port m)

theorem affine_iff (ho : ∀j,Odd (∑i,I.bundleSize (ports i) j)) :
    Affine (E.product (fun i=>R.uniform (f i)) ports) ↔ Affine (R.uniform (E.product f ports)) := by
  have hh : ∀j,Odd (E.count (E.portFamily ports) j) := by
    intro j
    rw [E.count_family]
    exact ho j
  have hv : E.product (fun i=>R.uniform (f i)) ports=
      fun z=>E.gauge (E.portFamily ports) z*E.product f ports z := funext (E.uniform_value f ports)
  rw [hv]
  exact gauge_affine_iff (E.portFamily ports) hh (E.product f ports)

theorem actual_uniform_nonaffine (ho : ∀j,Odd (∑i,I.bundleSize (ports i) j))
    (h : ¬Affine (E.product (fun i=>R.uniform (f i)) ports)) :
    ¬Affine (R.uniform (E.product f ports)) := fun ha=>h ((affine_iff f ports ho).mpr ha)
end Rows

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsUniformOdd
end
