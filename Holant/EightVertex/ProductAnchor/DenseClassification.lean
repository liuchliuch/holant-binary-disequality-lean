import Holant.EightVertex.ProductAnchor.GeneralizedEquality

namespace Holant.EightVertex.ProductAnchor
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

@[simp] theorem weight_zero_four : Holant.weight (fun _ : Fin 4 => false)=0 := by decide
@[simp] theorem weight_one_four : Holant.weight (fun _ : Fin 4 => true)=4 := by decide
@[simp] theorem bitSign_zero (s : Word4) : bitSign s (fun _ => false)=1 := by simp [bitSign]

theorem balanced_odd_balance (a c r A B : Scalar) (ha : a≠0) (hc : c≠0) (s : Word4)
    (he : EndpointEven (Signature.coordinateAction (fun _ => balanced a c r) (ge4 A B s))) :
    A*r^(Holant.weight s)=B*r^(4-Holant.weight s) := by
  have H := he.2.2 (![true,false,false,false]) (by decide)
  rw [action_balanced_ge4] at H
  have hw : Holant.weight (![true,false,false,false]:Word4)=1 := by decide
  rw [hw] at H
  norm_num only [Nat.reduceSub,pow_one,mul_neg_one] at H
  have hn : a^3*c*bitSign s (![true,false,false,false])≠0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) hc) (bitSign_ne_zero _ _)
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp H).resolve_left hn

theorem balanced_endpoint_value (a c r A B : Scalar) (s : Word4)
    (hb : A*r^(Holant.weight s)=B*r^(4-Holant.weight s)) :
    Signature.coordinateAction (fun _ => balanced a c r) (ge4 A B s) (fun _ => false)=
      2*A*r^(Holant.weight s)*a^4 := by
  rw [action_balanced_ge4]
  simp only [weight_zero_four,bitSign_zero,Nat.sub_zero,pow_zero,mul_one]
  rw [←hb]
  ring

/-- The dense form and both nonzero input coefficients are derived from odd
zeros and nonzero endpoints; no coefficient relation is assumed. -/
theorem balanced_ge_dense (a c r A B : Scalar) (ha : a≠0) (hc : c≠0) (hr : r≠0)
    (s : Word4) (he : EndpointEven
      (Signature.coordinateAction (fun _ => balanced a c r) (ge4 A B s))) :
    A≠0 ∧ B≠0 ∧ DenseForm (Signature.coordinateAction (fun _ => balanced a c r) (ge4 A B s)) := by
  have hb := balanced_odd_balance a c r A B ha hc s he
  have hval := balanced_endpoint_value a c r A B s hb
  have hA : A≠0 := by
    intro hz
    have h0 := he.1
    rw [hval,hz] at h0
    simp at h0
  have hB : B≠0 := by
    intro hz
    rw [hz,zero_mul] at hb
    exact mul_ne_zero hA (pow_ne_zero _ hr) hb
  refine ⟨hA,hB,2*A*r^(Holant.weight s)*a^4,c/a,?_,div_ne_zero hc ha,s,?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA) (pow_ne_zero _ hr)) (pow_ne_zero _ ha)
  · intro x
    by_cases hx : Holant.weight x%2=0
    · rw [if_pos hx,action_balanced_ge4,row_weight_ratio a c ha,
        (Nat.even_iff.mpr hx).neg_one_pow,←hb]
      ring
    · have ho : Holant.weight x%2=1 := by omega
      rw [if_neg hx]
      exact he.2.2 x ho

theorem DenseForm.nonzero_iff_even {q : Signature Scalar 4} (h : DenseForm q) (x : Word4) :
    q x≠0 ↔ Holant.weight x%2=0 := by
  obtain ⟨rho,r,hrho,hr,s,H⟩ := h
  rw [H x]
  by_cases hx : Holant.weight x%2=0
  · simp only [hx,ite_true,iff_true]
    exact mul_ne_zero (mul_ne_zero hrho (pow_ne_zero _ hr)) (bitSign_ne_zero s x)
  · simp [hx]

theorem DenseForm.support_card {q : Signature Scalar 4} (h : DenseForm q) :
    ((Finset.univ : Finset Word4).filter fun x => q x≠0).card=8 := by
  have he : ((Finset.univ : Finset Word4).filter fun x => q x≠0)=
      Finset.univ.filter (fun x : Word4 => Holant.weight x%2=0) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,h.nonzero_iff_even]
  rw [he]
  decide

end
end Holant.EightVertex.ProductAnchor
