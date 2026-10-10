import Holant.Tractable.Criteria
import Holant.Tractable.Anchor.MatrixActions

/-! Actual conformal kernels and their wordwise tensor action. -/
namespace Holant.Tractable
noncomputable section

/-- The literal bilinear conformal orthogonal condition for the disequality edge. -/
def XConformal (D : InvertibleKernel) : Prop :=
  ∃ c : AlgebraicComplex, c ≠ 0 ∧
    Kernel.pullback Signature.disequality D.matrix =
      fun a b => c * Signature.disequality a b

/-- The source's diagonal-or-antidiagonal classification follows from all four
entries of the actual bilinear pullback equation. -/
theorem XConformal.diagonal_or_antidiagonal {D : InvertibleKernel}
    (hD : XConformal D) :
    ∃ s t : AlgebraicComplex, s ≠ 0 ∧ t ≠ 0 ∧
      (D.matrix = diagonalKernel s t ∨
       D.matrix = Kernel.mul (diagonalKernel s t) Signature.disequality) := by
  obtain ⟨c, hc, he⟩ := hD
  have h00 := congrFun (congrFun he false) false
  have h11 := congrFun (congrFun he true) true
  have h01 := congrFun (congrFun he false) true
  simp [Kernel.pullback, Kernel.mul_apply, Kernel.transpose_apply,
    Signature.disequality] at h00 h11 h01
  have hac : D.matrix false false * D.matrix true false = 0 := by
    linear_combination h00 / 2
  have hbd : D.matrix false true * D.matrix true true = 0 := by
    linear_combination h11 / 2
  have hsum : D.matrix false false * D.matrix true true +
      D.matrix false true * D.matrix true false = c := by linear_combination h01
  rcases mul_eq_zero.mp hac with ha | hd
  · have hb : D.matrix false true ≠ 0 := by
      intro hb; apply hc; rw [ha, hb] at hsum; simpa using hsum.symm
    have hcc : D.matrix true false ≠ 0 := by
      intro hcc; apply hc; rw [ha, hcc] at hsum; simpa using hsum.symm
    have hee : D.matrix true true = 0 := (mul_eq_zero.mp hbd).resolve_left hb
    refine ⟨D.matrix false true, D.matrix true false, hb, hcc, Or.inr ?_⟩
    funext a b
    cases a <;> cases b <;> simp [Kernel.mul_apply, diagonalKernel,
      Signature.disequality, ha, hee]
  · have ha : D.matrix false false ≠ 0 := by
      intro ha; apply hc; rw [ha, hd] at hsum; simpa using hsum.symm
    have hee : D.matrix true true ≠ 0 := by
      intro hee; apply hc; rw [hee, hd] at hsum; simpa using hsum.symm
    have hb : D.matrix false true = 0 := (mul_eq_zero.mp hbd).resolve_right hee
    refine ⟨D.matrix false false, D.matrix true true, ha, hee, Or.inl ?_⟩
    funext a b
    cases a <;> cases b <;> simp [diagonalKernel, hb, hd]

/-- Complement every original, ordered port. -/
def complementWord {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun j => !(x j)

@[simp] theorem complementWord_involutive {n : ℕ} (x : Fin n → Bool) :
    complementWord (complementWord x) = x := by funext j; simp [complementWord]

/-- Exact coefficient of a diagonal tensor action before grouping by weight. -/
def diagonalCoefficient {n : ℕ} (s t : AlgebraicComplex) (x : Fin n → Bool) :
    AlgebraicComplex := ∏ j, if x j then t else s

theorem diagonalCoefficient_ne_zero {n : ℕ} {s t : AlgebraicComplex}
    (hs : s ≠ 0) (ht : t ≠ 0) (x : Fin n → Bool) :
    diagonalCoefficient s t x ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  cases x j <;> assumption

theorem coordinateAction_diagonal {n : ℕ} (s t : AlgebraicComplex)
    (f : Signature AlgebraicComplex n) :
    Signature.coordinateAction (fun _ => diagonalKernel s t) f =
      fun x => diagonalCoefficient s t x * f x := by
  classical
  funext x
  unfold Signature.coordinateAction
  have hprod (y : Fin n → Bool) :
      (∏ j, diagonalKernel s t (x j) (y j)) =
      diagonalCoefficient s t x * (if x = y then 1 else 0) := by
    calc
      _ = (∏ j, (if x j then t else s) *
          Signature.equality (K := AlgebraicComplex) (x j) (y j)) := by
        apply Finset.prod_congr rfl
        intro j _
        simp only [diagonalKernel, Signature.equality]
        split <;> simp_all
      _ = _ := by rw [Finset.prod_mul_distrib, Signature.prod_equality]; rfl
  simp only [hprod]
  simp

theorem coordinateAction_disequality {n : ℕ} (f : Signature AlgebraicComplex n) :
    Signature.coordinateAction (fun _ => Signature.disequality) f =
      fun x => f (complementWord x) := by
  classical
  funext x
  unfold Signature.coordinateAction
  have hprod (y : Fin n → Bool) :
      (∏ j, Signature.disequality (K := AlgebraicComplex) (x j) (y j)) =
      if complementWord x = y then 1 else 0 := by
    convert Signature.prod_equality (K := AlgebraicComplex) (complementWord x) y using 1
    apply Finset.prod_congr rfl
    intro j _
    cases hx : x j <;> cases y j <;>
      simp [Signature.disequality, Signature.equality, complementWord, hx]
  simp only [hprod]
  simp

theorem coordinateAction_antidiagonal {n : ℕ} (s t : AlgebraicComplex)
    (f : Signature AlgebraicComplex n) :
    Signature.coordinateAction
      (fun _ => Kernel.mul (diagonalKernel s t) Signature.disequality) f =
      fun x => diagonalCoefficient s t x * f (complementWord x) := by
  rw [← Signature.coordinateAction_comp, coordinateAction_disequality,
    coordinateAction_diagonal]

theorem diagonalCoefficient_eq_weight {n : ℕ} (s t : AlgebraicComplex)
    (x : Fin n → Bool) :
    diagonalCoefficient s t x = s ^ (n - Holant.weight x) * t ^ Holant.weight x := by
  classical
  have htrue : (Finset.univ.filter fun j : Fin n => x j = true).card =
      Holant.weight x := by
    simp only [Holant.weight, Finset.card_filter]
  have hfalse : (Finset.univ.filter fun j : Fin n => x j = false).card =
      n - Holant.weight x := by
    have hadd := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun j : Fin n => x j = true)
    have hn : (Finset.univ.filter fun j : Fin n => ¬ x j = true) =
        Finset.univ.filter fun j : Fin n => x j = false := by ext j; cases x j <;> simp
    rw [hn, htrue] at hadd
    simpa using (Nat.eq_sub_of_add_eq' hadd)
  unfold diagonalCoefficient
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [htrue]
  have hf : (Finset.univ.filter fun j : Fin n => ¬(x j = true)).card =
      n - Holant.weight x := by
    convert hfalse using 2
    ext j; cases x j <;> simp
  rw [hf]
  exact mul_comm _ _

/-- In particular, a diagonal action has one constant multiplier on an actual
single-layer signature, including its zero entries off the chosen layer. -/
theorem coordinateAction_diagonal_singleLayer {n d : ℕ} (s t : AlgebraicComplex)
    {f : Signature AlgebraicComplex n} (hf : Signature.SingleLayer f d) :
    Signature.coordinateAction (fun _ => diagonalKernel s t) f =
      fun x => (s ^ (n - d) * t ^ d) * f x := by
  rw [coordinateAction_diagonal]
  funext x
  by_cases hx : Holant.weight x = d
  · rw [diagonalCoefficient_eq_weight, hx]
  · simp [hf x hx]

/-- Support is unchanged in the diagonal case and exactly complemented in the
antidiagonal case. All coefficients remain nonzero. -/
theorem XConformal.support_action {D : InvertibleKernel} (hD : XConformal D) :
    (∀ n (f : Signature AlgebraicComplex n) x, D.action f x ≠ 0 ↔ f x ≠ 0) ∨
    (∀ n (f : Signature AlgebraicComplex n) x,
      D.action f x ≠ 0 ↔ f (complementWord x) ≠ 0) := by
  obtain ⟨s, t, hs, ht, h | h⟩ := hD.diagonal_or_antidiagonal
  · left
    intro n f x
    change Signature.coordinateAction (fun _ => D.matrix) f x ≠ 0 ↔ _
    rw [h, coordinateAction_diagonal]
    exact mul_ne_zero_iff.trans (and_iff_right (diagonalCoefficient_ne_zero hs ht x))
  · right
    intro n f x
    change Signature.coordinateAction (fun _ => D.matrix) f x ≠ 0 ↔ _
    rw [h, coordinateAction_antidiagonal]
    exact mul_ne_zero_iff.trans (and_iff_right (diagonalCoefficient_ne_zero hs ht x))

end
end Holant.Tractable
