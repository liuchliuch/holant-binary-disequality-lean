import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsPins
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineRankOne

/-! Uniform octic twisting preserves Affine membership of an actual finite
signed/pinned row product when each exposed variable has even total original
incidence. The multiplier is a nonzero constant times affine unary gauges.
This is a coefficient-product theorem only: no private summation is commuted
with a twist and no physical octic vertex is introduced. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsUniform
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeSignedPortsCore
open scoped BigOperators
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

variable {m : ℕ}
def phase (b : Bool) : AlgebraicComplex := if b then zetaEight else 1
def read (p : Port m) (z : Fin m→Bool) : Bool :=
  match p with | .inl b=>b | .inr (j,s)=>s ^^ z j
def constant (p : Port m) : AlgebraicComplex :=
  match p with | .inl b=>phase b | .inr _=>1
def axis (p : Port m) (j : Fin m) (b : Bool) : AlgebraicComplex :=
  match p with | .inl _=>1 | .inr (k,s)=>if k=j then phase (s ^^ b) else 1
def incidence (p : Port m) (j : Fin m) : ℕ :=
  match p with | .inl _=>0 | .inr (k,_)=>if k=j then 1 else 0

theorem phase_ne_zero (b : Bool) : phase b≠0 := by
  cases b <;> simp [phase,zetaEight_ne_zero]
theorem axis_ne_zero (p : Port m) (j : Fin m) (b : Bool) : axis p j b≠0 := by
  cases p with
  | inl c=>simp [axis]
  | inr q=>rcases q with ⟨k,s⟩;simp only [axis];split_ifs <;> simp [phase_ne_zero]

theorem port_factor (p : Port m) (z : Fin m→Bool) :
    phase (read p z)=constant p*∏j,axis p j (z j) := by
  cases p with
  | inl b=>simp [read,constant,axis]
  | inr q=>rcases q with ⟨k,s⟩;simp [read,constant,axis]

theorem axis_fourth (p : Port m) (j : Fin m) :
    axis p j false^4=(-1 : AlgebraicComplex)^incidence p j*axis p j true^4 := by
  cases p with
  | inl b=>simp [axis,incidence]
  | inr q=>
    rcases q with ⟨k,s⟩
    by_cases hk : k=j <;> cases s <;> simp [axis,incidence,phase,hk,zetaEight_pow_four]

variable {A : Type*} [Fintype A] (p : A→Port m)
def count (j : Fin m) : ℕ := ∑i,incidence (p i) j
def gauge (z : Fin m→Bool) : AlgebraicComplex := ∏i,phase (read (p i) z)
def scalar : AlgebraicComplex := ∏i,constant (p i)
def axisGauge (j : Fin m) (b : Bool) : AlgebraicComplex := ∏i,axis (p i) j b

theorem gauge_factor (z : Fin m→Bool) :
    gauge p z=scalar p*∏j,axisGauge p j (z j) := by
  simp only [gauge,port_factor,Finset.prod_mul_distrib,scalar,axisGauge]
  rw [Finset.prod_comm]

theorem gauge_ne_zero (z : Fin m→Bool) : gauge p z≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact phase_ne_zero _

theorem axisGauge_ne_zero (j : Fin m) (b : Bool) : axisGauge p j b≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact axis_ne_zero _ _ _

theorem axisGauge_fourth (j : Fin m) (he : Even (count p j)) :
    axisGauge p j false^4=axisGauge p j true^4 := by
  simp only [axisGauge,←Finset.prod_pow,axis_fourth,Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  change (-1 : AlgebraicComplex)^count p j*(∏i,axis (p i) j true^4)=_
  rw [he.neg_one_pow,one_mul]

theorem axisGauge_affine (j : Fin m) (he : Even (count p j)) :
    Affine (fun z : Fin m→Bool=>axisGauge p j (z j)) := by
  convert R.unary_of_equal_fourth_powers j (axisGauge p j false) (axisGauge p j true)
    (axisGauge_ne_zero p j false) (axisGauge_fourth p j he) using 1
  funext z
  cases z j <;> rfl

theorem affine_prod {B : Type*} [DecidableEq B] (S : Finset B)
    (f : B→Signature AlgebraicComplex m) (h : ∀i∈S,Affine (f i)) :
    Affine (fun z=>∏i∈S,f i z) := by
  induction S using Finset.induction_on with
  | empty=>simpa using affine_constant m 1
  | insert i S hi ih=>
    have ha := h i (by simp)
    have hb := ih (fun j hj=>h j (by simp [hj]))
    simpa only [Finset.prod_insert hi] using ha.mul hb

theorem gauge_affine (he : ∀j,Even (count p j)) : Affine (gauge p) := by
  have hp := affine_prod Finset.univ (fun j=>fun z : Fin m→Bool=>axisGauge p j (z j))
    (fun j _=>axisGauge_affine p j (he j))
  convert hp.scale (scalar p) using 1
  funext z
  exact gauge_factor p z

theorem gauge_inverse_affine (he : ∀j,Even (count p j)) : Affine (fun z=>(gauge p z)⁻¹) :=
  R.affine_inverse _ (gauge_affine p he)

theorem gauge_affine_iff (he : ∀j,Even (count p j)) (f : Signature AlgebraicComplex m) :
    Affine (fun z=>gauge p z*f z) ↔ Affine f := by
  constructor
  · intro h
    convert (gauge_inverse_affine p he).mul h using 1
    funext z
    rw [←mul_assoc,inv_mul_cancel₀ (gauge_ne_zero p z),one_mul]
  · intro h
    exact (gauge_affine p he).mul h

section Rows
variable {r : ℕ} {n : Fin r→ℕ}
variable (f : (i : Fin r)→Signature AlgebraicComplex (n i))
variable (ports : (i : Fin r)→Fin (n i)→Port m)

def portFamily : (Σi : Fin r,Fin (n i))→Port m := fun i=>ports i.1 i.2
def product : Signature AlgebraicComplex m := fun z=>∏i,f i (word (ports i) z)

theorem count_family (j : Fin m) : count (portFamily ports) j=∑i,I.bundleSize (ports i) j := by
  rw [count,Fintype.sum_sigma]
  rfl

theorem uniform_value (z : Fin m→Bool) :
    product (fun i=>R.uniform (f i)) ports z=gauge (portFamily ports) z*product f ports z := by
  simp only [product,R.uniform,localTwist_apply,Bool.true_and]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [gauge,Fintype.prod_sigma]
  rfl

theorem affine_iff (he : ∀j,Even (∑i,I.bundleSize (ports i) j)) :
    Affine (product (fun i=>R.uniform (f i)) ports) ↔ Affine (product f ports) := by
  have hh : ∀j,Even (count (portFamily ports) j) := by
    intro j
    rw [count_family]
    exact he j
  have hv : product (fun i=>R.uniform (f i)) ports=fun z=>gauge (portFamily ports) z*product f ports z :=
    funext (uniform_value f ports)
  rw [hv]
  exact gauge_affine_iff (portFamily ports) hh (product f ports)

theorem actual_nonaffine (he : ∀j,Even (∑i,I.bundleSize (ports i) j))
    (h : ¬Affine (product (fun i=>R.uniform (f i)) ports)) : ¬Affine (product f ports) :=
  fun ha=>h ((affine_iff f ports he).mpr ha)

end Rows
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSignedRowsUniform
end
