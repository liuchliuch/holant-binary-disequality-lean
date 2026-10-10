import Holant.EightVertex.ProductAnchor.FactorArity

/-! Even support of the actual tensor product forces its two binary factors
onto equality support, with both endpoint coefficients genuinely nonzero. -/
namespace Holant.EightVertex.ProductAnchor
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def factorWord (D : TensorDecomposition Scalar 4) (i : Fin D.count)
    (y : Fin (D.arity i) → Bool) : Word4 :=
  D.assignments.symm (Function.update (fun j (_ : Fin (D.arity j)) => false) i y)

 theorem factorWord_blocks (D : TensorDecomposition Scalar 4) (i : Fin D.count)
    (y : Fin (D.arity i) → Bool) (j : Fin D.count) :
    (fun k => factorWord D i y (D.ports ⟨j,k⟩)) =
      Function.update (fun j (_ : Fin (D.arity j)) => false) i y j := by
  funext k
  have H := congrFun (congrFun (D.assignments.apply_symm_apply
    (Function.update (fun j (_ : Fin (D.arity j)) => false) i y)) j) k
  simpa only [TensorDecomposition.assignments_apply, factorWord] using H

 theorem factorWord_weight (D : TensorDecomposition Scalar 4) (i : Fin D.count)
    (y : Fin (D.arity i) → Bool) : Holant.weight (factorWord D i y)=Holant.weight y := by
  unfold Holant.weight
  rw [←Equiv.sum_comp D.ports (fun p : Fin 4 => if factorWord D i y p then 1 else 0)]
  rw [Fintype.sum_sigma]
  change (∑ j, Holant.weight (fun k => factorWord D i y (D.ports ⟨j,k⟩))) = _
  simp_rw [factorWord_blocks]
  rw [Finset.sum_eq_single i]
  · simp [Holant.weight]
  · intro j _ hji
    simp [Function.update_of_ne hji,Holant.weight]
  · simp

 theorem factor_odd_zero (D : TensorDecomposition Scalar 4) (he : EndpointEven D.value)
    (i : Fin D.count) (y : Fin (D.arity i) → Bool) (hy : Holant.weight y%2=1) :
    D.factor i y=0 := by
  by_contra hn
  have hz := he.2.2 (factorWord D i y) (by rw [factorWord_weight]; exact hy)
  have hne : D.value (factorWord D i y)≠0 := by
    unfold TensorDecomposition.value
    apply mul_ne_zero D.scale.ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [factorWord_blocks]
    by_cases hji : j=i
    · subst j; simpa using hn
    · simpa [Function.update_of_ne hji] using factor_false_ne_zero D he j
  exact hne hz

 theorem binary_nonconstant_odd (y : Fin 2 → Bool)
    (h0 : y≠fun _ => false) (h1 : y≠fun _ => true) : Holant.weight y%2=1 := by
  revert y
  decide

 theorem two_factor_equality (D : TensorDecomposition Scalar 4) (he : EndpointEven D.value)
    (hc : D.count=2) (hp : ∀ i,0<D.arity i) (i : Fin D.count)
    (y : Fin (D.arity i) → Bool) :
    D.factor i y = (if y=(fun _ => false) then D.factor i (fun _ => false) else 0) +
      (if y=(fun _ => true) then D.factor i (fun _ => true) else 0) := by
  have har := two_factor_arities D he hc hp i
  have hcst : (fun _ : Fin (D.arity i) => false)≠(fun _ => true) := by
    intro h
    have hi : 0<D.arity i := hp i
    have h' := congrFun h ⟨0,hi⟩
    exact Bool.false_ne_true h'
  by_cases h0 : y=(fun _ => false)
  · simp [h0,hcst]
  by_cases h1 : y=(fun _ => true)
  · simp [h1,Ne.symm hcst]
  have hodd : Holant.weight y%2=1 := by
    have H (n : ℕ) (hn : n=2) (x : Fin n → Bool)
        (hx0 : x≠fun _ => false) (hx1 : x≠fun _ => true) : Holant.weight x%2=1 := by
      subst n
      exact binary_nonconstant_odd x hx0 hx1
    exact H _ har y h0 h1
  simp [h0,h1,factor_odd_zero D he i y hodd]

/-- The actual ordered two-block factorization consists of nonsingular weighted
binary equalities. The original scale and every original port are retained. -/
def TwoWeightedEqualities (q : Signature Scalar 4) : Prop :=
  ∃ D : TensorDecomposition Scalar 4, D.count=2 ∧ (∀ i,D.arity i=2) ∧ D.value=q ∧
    (∀ i,D.factor i (fun _ => false)≠0 ∧ D.factor i (fun _ => true)≠0) ∧
    ∀ i y, D.factor i y =
      (if y=(fun _ => false) then D.factor i (fun _ => false) else 0) +
      (if y=(fun _ => true) then D.factor i (fun _ => true) else 0)

 theorem two_weighted_equalities_of_decomposition (q : Signature Scalar 4)
    (he : EndpointEven q) (D : TensorDecomposition Scalar 4)
    (hc : D.count=2) (hp : ∀ i,0<D.arity i) (hq : D.value=q) : TwoWeightedEqualities q := by
  have he' : EndpointEven D.value := hq.symm ▸ he
  exact ⟨D,hc,two_factor_arities D he' hc hp,hq,
    fun i => ⟨factor_false_ne_zero D he' i,factor_true_ne_zero D he' i⟩,
    two_factor_equality D he' hc hp⟩

end
end Holant.EightVertex.ProductAnchor
