import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorCriterion
import Holant.EightVertex.ProductAnchor.MatrixForms
import Holant.EightVertex.ProductAnchor.ProductComponentsSupport
import Holant.Tractable.Conformal.MatrixSupport

/-! Rigidity of a genuine invertible basis taking literal Eq4 into the actual
Product class. The proof uses the unrestricted ProductFactor list. A supported
mixed Hamming layer excludes every nontrivial binary factor; its two slice
minors then force the basis to be monomial. No prime-factor or normal-form
hypothesis is added. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorProductBasis
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open Holant.EightVertex.ProductAnchor
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev eq4 := StableHigherCurrentAnchorCriterion.eq4

/-- The five symmetric coefficients of an actual tensor transform of Eq4. -/
def coefficient (T : Kernel AlgebraicComplex) (k : ℕ) : AlgebraicComplex :=
  T false false ^ (4-k) * T true false ^ k +
    T false true ^ (4-k) * T true true ^ k

theorem action_eq4_weight (T : InvertibleKernel) (x : Fin 4 → Bool) :
    T.action eq4 x = coefficient T.matrix (Holant.weight x) := by
  rw [InvertibleKernel.action, StableHigherCurrentAnchorCriterion.action_eq4]
  have hp (b : Bool) : (∏ i, T.matrix (x i) b) =
      diagonalCoefficient (T.matrix false b) (T.matrix true b) x := by
    apply Finset.prod_congr rfl
    intro i _
    cases x i <;> rfl
  rw [hp false, hp true, diagonalCoefficient_eq_weight, diagonalCoefficient_eq_weight]
  rfl

/-- Every mixed four-bit layer contains a word disagreeing on any distinct
pair, and a word agreeing on any pair. This finite fact is independent of values. -/
theorem mixed_layer_disagree (k : ℕ) (hk0 : 0 < k) (hk4 : k < 4)
    (i j : Fin 4) (hij : i ≠ j) :
    ∃ x : Fin 4 → Bool, Holant.weight x = k ∧ x i ≠ x j := by
  interval_cases k <;> revert i j <;> decide

theorem mixed_layer_agree (k : ℕ) (hk0 : 0 < k) (hk4 : k < 4)
    (i j : Fin 4) :
    ∃ x : Fin 4 → Bool, Holant.weight x = k ∧ x i = x j := by
  interval_cases k <;> revert i j <;> decide

/-- Rank-one minor for the first two ports, with the other two fixed. -/
def SliceRankOne (f : Signature AlgebraicComplex 4) : Prop := ∀ u v : Bool,
  f ![false,false,u,v] * f ![true,true,u,v] =
    f ![false,true,u,v] * f ![true,false,u,v]

theorem sliceRankOne_mul {f g : Signature AlgebraicComplex 4}
    (hf : SliceRankOne f) (hg : SliceRankOne g) :
    SliceRankOne (fun x => f x * g x) := by
  intro u v
  calc
    _ = (f ![false,false,u,v] * f ![true,true,u,v]) *
        (g ![false,false,u,v] * g ![true,true,u,v]) := by ring
    _ = _ := by rw [hf u v,hg u v]; ring

/-- A supported mixed layer forces every actual product factor to be unary
or a repeated equality. Therefore every first-two-port slice has rank at most one. -/
theorem product_mixed_layer_rankOne (f : Signature AlgebraicComplex 4)
    (hf : Product f) (k : ℕ) (hk0 : 0 < k) (hk4 : k < 4)
    (hs : ∀ x, Holant.weight x = k → f x ≠ 0) : SliceRankOne f := by
  rcases hf with hz | ⟨a,ha,ps,rfl⟩
  · obtain ⟨x,hx,_⟩ := mixed_layer_agree k hk0 hk4 0 0
    exact False.elim (hs x hx (by simp [hz]))
  have hfactor (p : ProductFactor 4) (hp : p ∈ ps) : SliceRankOne p.eval := by
    cases p with
    | unary i vals hvals =>
        intro u v
        fin_cases i <;> simp [ProductFactor.eval,mul_comm]
    | equality i j =>
        by_cases hij : i=j
        · subst j
          intro u v
          simp [ProductFactor.eval,Signature.equality]
        · obtain ⟨x,hx,hijx⟩ := mixed_layer_disagree k hk0 hk4 i j hij
          have hn := factor_nonzero_of_formula_nonzero a ps x (hs x hx) (.equality i j) hp
          exact False.elim (hn (by simp [ProductFactor.eval,Signature.equality,hijx]))
    | disequality i j =>
        obtain ⟨x,hx,hijx⟩ := mixed_layer_agree k hk0 hk4 i j
        have hn := factor_nonzero_of_formula_nonzero a ps x (hs x hx) (.disequality i j) hp
        exact False.elim (hn (by simp [ProductFactor.eval,Signature.disequality,hijx]))
  clear hs ha
  have H : SliceRankOne (fun x => (ps.map (fun p => p.eval x)).prod) := by
    induction ps with
    | nil => intro u v; simp
    | cons p ps ih =>
        have hp := hfactor p (by simp)
        have hps := ih (fun q hq => hfactor q (by simp [hq]))
        simpa only [List.map_cons,List.prod_cons] using sliceRankOne_mul hp hps
  exact sliceRankOne_mul (f := fun _ => a) (by intro u v; rfl) H

private theorem monomial_of_row_products (T : InvertibleKernel)
    (h0 : T.matrix false false * T.matrix false true = 0)
    (h1 : T.matrix true false * T.matrix true true = 0) : Monomial T.matrix := by
  have hd := determinant_ne_zero T
  rcases mul_eq_zero.mp h0 with ha | hb <;> rcases mul_eq_zero.mp h1 with hc | hd'
  · exact False.elim (hd (by simp [determinant,ha,hc]))
  · exact Or.inr ⟨ha,hd'⟩
  · exact Or.inl ⟨hb,hc⟩
  · exact False.elim (hd (by simp [determinant,hb,hd']))

/-- The two endpoint slice determinants recover both row products exactly. -/
theorem monomial_of_sliceRankOne (T : InvertibleKernel)
    (h : SliceRankOne (T.action eq4)) : Monomial T.matrix := by
  have h0 := h false false
  have h1 := h true true
  simp [InvertibleKernel.action,StableHigherCurrentAnchorCriterion.action_eq4,
    Fin.prod_univ_succ] at h0 h1
  have hd := determinant_ne_zero T
  have p0 : (T.matrix false false * T.matrix false true * determinant T.matrix)^2 = 0 := by
    unfold determinant
    linear_combination h0
  have p1 : (T.matrix true false * T.matrix true true * determinant T.matrix)^2 = 0 := by
    unfold determinant
    linear_combination h1
  apply monomial_of_row_products T
  · exact (mul_eq_zero.mp (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp p0)).resolve_right hd
  · exact (mul_eq_zero.mp (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp p1)).resolve_right hd

/-- If all three mixed coefficients vanish, nonsingularity itself forces a
monomial basis; the crucial middle minor is abcd times the squared determinant. -/
theorem monomial_of_mixed_zero (T : InvertibleKernel)
    (h1 : coefficient T.matrix 1 = 0) (h2 : coefficient T.matrix 2 = 0)
    (h3 : coefficient T.matrix 3 = 0) : Monomial T.matrix := by
  have hd := determinant_ne_zero T
  have hp : T.matrix false false * T.matrix false true *
      T.matrix true false * T.matrix true true * (determinant T.matrix)^2 = 0 := by
    unfold determinant
    norm_num [coefficient] at h1 h2 h3
    linear_combination (T.matrix false false * T.matrix true false^3 +
      T.matrix false true * T.matrix true true^3) * h1 -
      (T.matrix false false^2 * T.matrix true false^2 +
        T.matrix false true^2 * T.matrix true true^2) * h2
  have hz := (mul_eq_zero.mp hp).resolve_right (pow_ne_zero 2 hd)
  norm_num [coefficient] at h1 h2 h3
  rcases mul_eq_zero.mp hz with habc | hd'
  · rcases mul_eq_zero.mp habc with hab | hc
    · rcases mul_eq_zero.mp hab with ha | hb
      · right
        refine ⟨ha,?_⟩
        have hb : T.matrix false true ≠ 0 := by intro hb; exact hd (by simp [determinant,ha,hb])
        simpa [ha,hb,pow_ne_zero 3 hb] using h1
      · left
        refine ⟨hb,?_⟩
        have ha : T.matrix false false ≠ 0 := by intro ha; exact hd (by simp [determinant,ha,hb])
        simpa [hb,ha] using h3
    · left
      refine ⟨?_,hc⟩
      have hdn : T.matrix true true ≠ 0 := by intro hd'; exact hd (by simp [determinant,hc,hd'])
      simpa [hc,hdn] using h1
  · right
    refine ⟨?_,hd'⟩
    have hc : T.matrix true false ≠ 0 := by intro hc; exact hd (by simp [determinant,hc,hd'])
    simpa [hd',hc,pow_ne_zero 3 hc] using h3

/-- Literal Eq4 admits only diagonal or antidiagonal invertible Product bases.
The source's actual Product predicate is sufficient, without using the edge. -/
theorem product_eq4_action_monomial (T : InvertibleKernel)
    (h : Product (T.action eq4)) : Monomial T.matrix := by
  by_cases hm : ∃ k : ℕ, 0 < k ∧ k < 4 ∧ coefficient T.matrix k ≠ 0
  · obtain ⟨k,hk0,hk4,hk⟩ := hm
    apply monomial_of_sliceRankOne T
    exact product_mixed_layer_rankOne _ h k hk0 hk4 (by
      intro x hx
      simpa [action_eq4_weight,hx] using hk)
  · apply monomial_of_mixed_zero T
    · by_contra hn; exact hm ⟨1,by decide,by decide,hn⟩
    · by_contra hn; exact hm ⟨2,by decide,by decide,hn⟩
    · by_contra hn; exact hm ⟨3,by decide,by decide,hn⟩

/-- The inverse has the same monomial support type, derived from the actual
inverse equations. -/
theorem monomial_inverse (T : InvertibleKernel) (h : Monomial T.matrix) :
    Monomial T.inverse := by
  have h01 := congrFun (congrFun T.matrix_inverse false) true
  have h10 := congrFun (congrFun T.matrix_inverse true) false
  have hd := determinant_ne_zero T
  rcases h with h | h
  · left
    have ha : T.matrix false false ≠ 0 := by
      intro ha
      exact hd (by simp [determinant,ha,h.1,h.2])
    have hb : T.matrix true true ≠ 0 := by
      intro hb
      exact hd (by simp [determinant,hb,h.1,h.2])
    simp [Kernel.mul_apply,Signature.equality,h.1,h.2,ha,hb] at h01 h10
    exact ⟨h01,h10⟩
  · right
    have ha : T.matrix false true ≠ 0 := by
      intro ha
      exact hd (by simp [determinant,ha,h.1,h.2])
    have hb : T.matrix true false ≠ 0 := by
      intro hb
      exact hd (by simp [determinant,hb,h.1,h.2])
    simp [Kernel.mul_apply,Signature.equality,h.1,h.2,ha,hb] at h01 h10
    exact ⟨h10,h01⟩

/-- A single Product witness for any family containing Eq4 has monomial
matrix and inverse. The mandatory edge remains part of IsCommonBasis. -/
theorem common_product_basis_monomial {F : SignatureFamily AlgebraicComplex}
    (mem : (⟨4,eq4⟩ : AnySignature AlgebraicComplex) ∈ F)
    (B : InvertibleKernel) (hB : IsCommonBasis productClass F B) :
    Monomial B.matrix ∧ Monomial B.inverse := by
  have hi := product_eq4_action_monomial B.symm (hB.2 _ mem)
  exact ⟨monomial_inverse B.symm hi,hi⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorProductBasis
end
