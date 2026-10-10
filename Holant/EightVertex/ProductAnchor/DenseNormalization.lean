import Holant.EightVertex.ProductAnchor.DenseNormalizationMatrix
import Holant.EightVertex.ProductAnchor.NetworksScaling
import Mathlib.Tactic.IntervalCases

namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def denseTensor (rho r : Scalar) (s : Word4) : Signature Scalar 4 := fun x =>
  if Holant.weight x%2=0 then rho*r^(Holant.weight x)*bitSign s x else 0

theorem denseTensor_balanced (rho r : Scalar) (s : Word4) :
    denseTensor rho r s=Signature.coordinateAction (fun _ => balanced 1 r 1)
      (ge4 (rho/2) (rho/2) s) := by
  funext x
  rw [action_balanced_ge4]
  simp only [one_pow,one_mul,mul_one]
  by_cases hx : Holant.weight x%2=0
  · rw [(Nat.even_iff.mpr hx).neg_one_pow]
    simp [denseTensor,hx]
    ring
  · have ho : Odd (Holant.weight x) := Nat.odd_iff.mpr (by omega)
    rw [ho.neg_one_pow]
    simp [denseTensor,hx]

theorem quarter_turn_complement (k : ℕ) (hk : k≤4) :
    imaginaryUnit^(4-k)=imaginaryUnit^k*(-1:Scalar)^k := by
  have h3 : imaginaryUnit^3= -imaginaryUnit := by
    calc
      _ = imaginaryUnit*imaginaryUnit^2 := by ring
      _ = _ := by simp
  interval_cases k <;> norm_num [imaginaryUnit_sq,imaginaryUnit_pow_four,h3]

theorem diagonal_normalization_coefficient (u : Scalar) (x : Word4) :
    diagonalCoefficient u (imaginaryUnit*u) x=u^4*imaginaryUnit^(Holant.weight x) := by
  rw [diagonalCoefficient_eq_weight,mul_pow]
  calc
    _ = (u^(4-Holant.weight x)*u^(Holant.weight x))*imaginaryUnit^(Holant.weight x) := by ring
    _ = _ := by rw [←pow_add,Nat.sub_add_cancel (Holant.weight_le x)]

def denseNormalizationScale (rho u : Scalar) (s : Word4) : Scalar :=
  (rho/2)*u^4*imaginaryUnit^(Holant.weight s)

theorem denseNormalizationScale_ne_zero (rho u : Scalar) (s : Word4)
    (hrho : rho≠0) (hu : u≠0) : denseNormalizationScale rho u s≠0 :=
  mul_ne_zero (mul_ne_zero (div_ne_zero hrho (by norm_num)) (pow_ne_zero _ hu))
    (pow_ne_zero _ imaginary_nonzero)

theorem diagonal_ge_normalized (rho u : Scalar) (s : Word4) :
    Signature.coordinateAction (fun _ => diagonalKernel u (imaginaryUnit*u))
      (ge4 (rho/2) (rho/2) s)=
    fun x => denseNormalizationScale rho u s * normalized s x := by
  funext x
  rw [coordinateAction_diagonal]
  change diagonalCoefficient u (imaginaryUnit*u) x * ge4 (rho/2) (rho/2) s x =
    denseNormalizationScale rho u s * ((if x=s then 1 else 0)+
      (-1:Scalar)^(Holant.weight s)*(if x=complementWord s then 1 else 0))
  rw [diagonal_normalization_coefficient]
  by_cases hx : x=s
  · subst x
    rw [ge4_left]
    simp only [ite_true,if_neg (word_ne_complement s),mul_zero,add_zero,mul_one]
    unfold denseNormalizationScale
    ring
  by_cases hy : x=complementWord s
  · subst x
    have hw : Holant.weight (complementWord s)=4-Holant.weight s := by
      have H := Holant.weight_compl_add s
      change Holant.weight (complementWord s)+Holant.weight s=4 at H
      omega
    rw [ge4_right,hw,quarter_turn_complement _ (Holant.weight_le s)]
    simp only [if_neg (Ne.symm (word_ne_complement s)),ite_true,mul_one,zero_add]
    unfold denseNormalizationScale
    ring
  · rw [ge4_outside _ _ _ _ hx hy]
    simp [hx,hy]

theorem normalize_denseTensor (rho r u : Scalar) (hr : r≠0) (s : Word4) :
    Signature.coordinateAction (fun _ => normalizationMatrix r u) (denseTensor rho r s)=
      fun x => denseNormalizationScale rho u s*normalized s x := by
  rw [denseTensor_balanced,Signature.coordinateAction_comp]
  simp_rw [normalization_times_balanced r u hr]
  exact diagonal_ge_normalized rho u s

/-- Exact source normal form: a genuine algebraic invertible matrix changes the
native edge to equality and the actual dense signature to a nonzero multiple of
Fs. This is a coordinate statement, not permission to use R as a physical gadget. -/
theorem dense_normal_form (q : Signature Scalar 4) (h : DenseForm q) :
    ∃ (R : InvertibleKernel) (eta : Scalar) (s : Word4), eta≠0 ∧
      Kernel.pullback Signature.disequality R.inverse=Signature.equality ∧
      R.action q=(fun x => eta*normalized s x) := by
  obtain ⟨rho,r,hrho,hr,s,H⟩ := h
  obtain ⟨u,hu,hsq⟩ := exists_algebraic_normalizing_root r hr
  refine ⟨denseNormalization r u hr hu,denseNormalizationScale rho u s,s,
    denseNormalizationScale_ne_zero rho u s hrho hu,normalization_edge r u hu hsq,?_⟩
  have hq : q=denseTensor rho r s := funext H
  rw [hq]
  exact normalize_denseTensor rho r u hr s

end
end Holant.EightVertex.ProductAnchor
