import Holant.EightVertex.ProductAnchor.GeneralizedEquality
import Holant.TensorAction

namespace Holant.EightVertex.ProductAnchor
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def blockTrueWord (D : TensorDecomposition Scalar 4) (i : Fin D.count) : Word4 :=
  fun p => decide ((D.ports.symm p).1=i)

theorem blockTrueWord_ports (D : TensorDecomposition Scalar 4) (i j : Fin D.count)
    (k : Fin (D.arity j)) : blockTrueWord D i (D.ports ⟨j,k⟩)=decide (j=i) := by
  simp [blockTrueWord]

theorem blockTrueWord_weight (D : TensorDecomposition Scalar 4) (i : Fin D.count) :
    Holant.weight (blockTrueWord D i)=D.arity i := by
  unfold Holant.weight blockTrueWord
  simp only [decide_eq_true_eq]
  rw [←Equiv.sum_comp D.ports (fun p : Fin 4 => if (D.ports.symm p).1=i then 1 else 0)]
  rw [Fintype.sum_sigma]
  simp

theorem factor_false_ne_zero (D : TensorDecomposition Scalar 4) (he : EndpointEven D.value)
    (i : Fin D.count) : D.factor i (fun _ => false)≠0 := by
  have h0 := he.1
  change (D.scale:Scalar)*(∏ j,D.factor j (fun _ => false))≠0 at h0
  exact Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp h0).2 i (Finset.mem_univ i)

theorem factor_true_ne_zero (D : TensorDecomposition Scalar 4) (he : EndpointEven D.value)
    (i : Fin D.count) : D.factor i (fun _ => true)≠0 := by
  have h1 := he.2.1
  change (D.scale:Scalar)*(∏ j,D.factor j (fun _ => true))≠0 at h1
  exact Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp h1).2 i (Finset.mem_univ i)

theorem blockTrueWord_value_ne_zero (D : TensorDecomposition Scalar 4) (he : EndpointEven D.value)
    (i : Fin D.count) : D.value (blockTrueWord D i)≠0 := by
  unfold TensorDecomposition.value
  apply mul_ne_zero D.scale.ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  simp only [blockTrueWord_ports]
  by_cases hji : j=i
  · simpa [hji] using factor_true_ne_zero D he j
  · simpa [hji] using factor_false_ne_zero D he j

theorem factor_arity_even (D : TensorDecomposition Scalar 4) (he : EndpointEven D.value)
    (i : Fin D.count) : D.arity i%2=0 := by
  have hne : D.arity i%2≠1 := by
    intro h
    have hz := he.2.2 (blockTrueWord D i) (by rw [blockTrueWord_weight]; exact h)
    exact blockTrueWord_value_ne_zero D he i hz
  omega

theorem factor_arity_sum (D : TensorDecomposition Scalar 4) :
    (∑ i,D.arity i)=4 := by
  have H := Fintype.card_congr D.ports
  simpa [Fintype.card_sigma] using H

/-- Nonzero endpoints and even parity force every positive block of a genuine
two-block decomposition to have arity2. No prime-factor oracle is assumed. -/
theorem two_factor_arities (D : TensorDecomposition Scalar 4) (he : EndpointEven D.value)
    (hc : D.count=2) (hp : ∀ i,0<D.arity i) : ∀ i,D.arity i=2 := by
  cases D with
  | mk count arity factor ports scale =>
    change count=2 at hc
    subst count
    let E : TensorDecomposition Scalar 4 := ⟨2,arity,factor,ports,scale⟩
    have hs := factor_arity_sum E
    have h0 := factor_arity_even E he 0
    have h1 := factor_arity_even E he 1
    have hp0 := hp 0
    have hp1 := hp 1
    simp only [E,Fin.sum_univ_two] at hs h0 h1
    intro i
    fin_cases i <;> dsimp at * <;> omega

end
end Holant.EightVertex.ProductAnchor
