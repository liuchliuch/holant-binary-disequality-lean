import Holant.Tractable.AffinePhase.Roots
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-! The nowhere-zero affine phase criterion, with Boolean addition interpreted as XOR. -/
namespace Holant.Tractable
noncomputable section

namespace AffinePhase

variable {n : ℕ}

abbrev Word (n : ℕ) := Fin n → Bool

def xor (x y : Word n) : Word n := fun j => Bool.xor (x j) (y j)

def origin (n : ℕ) : Word n := fun _ => false

def basis (j : Fin n) : Word n := fun k => decide (k = j)

@[simp] theorem xor_apply (x y : Word n) (j : Fin n) :
    xor x y j = Bool.xor (x j) (y j) := rfl
@[simp] theorem xor_self (x : Word n) : xor x x = origin n := by
  funext j; simp [xor, origin]
@[simp] theorem xor_origin (x : Word n) : xor x (origin n) = x := by
  funext j; simp [xor, origin]
@[simp] theorem origin_xor (x : Word n) : xor (origin n) x = x := by
  funext j; simp [xor, origin]
theorem xor_comm (x y : Word n) : xor x y = xor y x := by
  funext j; exact Bool.xor_comm _ _
theorem xor_assoc (x y z : Word n) : xor (xor x y) z = xor x (xor y z) := by
  funext j; exact Bool.xor_assoc _ _ _
@[simp] theorem xor_cancel_right (x y : Word n) : xor (xor x y) y = x := by
  rw [xor_assoc, xor_self, xor_origin]
@[simp] theorem xor_cancel_left (x y : Word n) : xor x (xor x y) = y := by
  rw [← xor_assoc, xor_self, origin_xor]

def thirdRatio (f : Signature AlgebraicComplex n) (z u v w : Word n) :
    AlgebraicComplex :=
  (f (xor (xor (xor z u) v) w) * f (xor z u) * f (xor z v) * f (xor z w)) /
  (f (xor (xor z u) v) * f (xor (xor z u) w) * f (xor (xor z v) w) * f z)

def secondRatio (f : Signature AlgebraicComplex n) (z u v : Word n) :
    AlgebraicComplex := f (xor (xor z u) v) * f z / (f (xor z u) * f (xor z v))

def ThirdTrivial (f : Signature AlgebraicComplex n) : Prop :=
  ∀ z u v w, thirdRatio f z u v w = 1

theorem thirdRatio_eq_one_iff {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (z u v w : Word n) :
    thirdRatio f z u v w = 1 ↔
      f (xor (xor (xor z u) v) w) * f (xor z u) * f (xor z v) * f (xor z w) =
      f (xor (xor z u) v) * f (xor (xor z u) w) * f (xor (xor z v) w) * f z := by
  exact div_eq_one_iff_eq (by exact mul_ne_zero (mul_ne_zero
    (mul_ne_zero (hf _) (hf _)) (hf _)) (hf _))

/-- Repeated directions force the normalized values to be fourth roots. -/
theorem normalized_pow_four {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : ThirdTrivial f) (x : Word n) :
    (f x / f (origin n)) ^ 4 = 1 := by
  have hh := (thirdRatio_eq_one_iff hf (origin n) x x x).mp (h _ _ _ _)
  simp only [origin_xor, xor_self] at hh
  have heq : f x ^ 4 = f (origin n) ^ 4 := by linear_combination hh
  rw [div_pow, heq, div_self (pow_ne_zero _ (hf _))]

/-- The third difference says exactly that every second difference is constant. -/
theorem secondRatio_constant {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : ThirdTrivial f) (z u v : Word n) :
    secondRatio f z u v = secondRatio f (origin n) u v := by
  have hh := (thirdRatio_eq_one_iff hf (origin n) u v z).mp (h _ _ _ _)
  simp only [origin_xor] at hh
  have h1 : xor (xor u v) z = xor (xor z u) v := by
    rw [xor_comm (xor u v) z, ← xor_assoc]
  have h2 : xor u z = xor z u := xor_comm _ _
  have h3 : xor v z = xor z v := xor_comm _ _
  rw [h1, h2, h3] at hh
  simp only [secondRatio, origin_xor]
  apply (div_eq_div_iff (mul_ne_zero (hf _) (hf _))
    (mul_ne_zero (hf _) (hf _))).mpr
  linear_combination hh

/-- Constant second differences on a Boolean group are signs. -/
theorem secondRatio_sq {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : ThirdTrivial f) (u v : Word n) :
    secondRatio f (origin n) u v ^ 2 = 1 := by
  have hh := secondRatio_constant hf h u u v
  simp only [secondRatio, origin_xor, xor_self] at hh
  have hc : f v * f u * (f u * f v) =
      f (xor u v) * f (origin n) * (f (origin n) * f (xor u v)) :=
    (div_eq_div_iff (mul_ne_zero (hf _) (hf _))
      (mul_ne_zero (hf _) (hf _))).mp hh
  simp only [secondRatio, origin_xor, div_pow]
  apply (div_eq_one_iff_eq (pow_ne_zero _ (mul_ne_zero (hf _) (hf _)))).mpr
  linear_combination -hc

/-- The coordinates of a finite set, interpreted as a Boolean word. -/
def word (s : Finset (Fin n)) : Word n := fun j => decide (j ∈ s)

@[simp] theorem word_empty : word (∅ : Finset (Fin n)) = origin n := by
  funext j; simp [word, origin]

@[simp] theorem word_singleton (j : Fin n) : word {j} = basis j := by
  funext k; simp [word, basis]

theorem word_insert (s : Finset (Fin n)) (j : Fin n) (hj : j ∉ s) :
    word (insert j s) = xor (word s) (basis j) := by
  funext k
  by_cases hk : k = j
  · subst k; simp [word, basis, xor, hj]
  · simp [word, basis, xor, hk]

/-- Source coefficient `A_j`. -/
def linearCoefficient (f : Signature AlgebraicComplex n) (j : Fin n) :
    AlgebraicComplex := f (basis j) / f (origin n)

/-- Source coefficient `B_jk`, extended symmetrically and also defined on the diagonal. -/
def mixedCoefficient (f : Signature AlgebraicComplex n) (j k : Fin n) :
    AlgebraicComplex := secondRatio f (origin n) (basis j) (basis k)

theorem mixedCoefficient_comm (f : Signature AlgebraicComplex n) (j k : Fin n) :
    mixedCoefficient f j k = mixedCoefficient f k j := by
  simp only [mixedCoefficient, secondRatio, origin_xor]
  rw [xor_comm (basis j) (basis k), mul_comm (f (basis j)) (f (basis k))]

/-- Translation multiplies a first difference by the constant second difference. -/
theorem firstRatio_translate {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : ThirdTrivial f) (z u v : Word n) :
    f (xor (xor z v) u) / f (xor z v) =
      secondRatio f (origin n) u v * (f (xor z u) / f z) := by
  have hh := secondRatio_constant hf h z u v
  have hc := (div_eq_iff (mul_ne_zero (hf (xor z u)) (hf (xor z v)))).mp hh
  have hswap : xor (xor z v) u = xor (xor z u) v := by
    rw [xor_assoc, xor_comm v u, ← xor_assoc]
  rw [hswap]
  field_simp [hf]
  linear_combination hc

/-- Hamming-weight induction reconstructs every first difference. -/
theorem firstRatio_word {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : ThirdTrivial f) (j : Fin n)
    (s : Finset (Fin n)) :
    f (xor (word s) (basis j)) / f (word s) =
      linearCoefficient f j * ∏ k ∈ s, mixedCoefficient f j k := by
  induction s using Finset.induction_on with
  | empty => simp [linearCoefficient]
  | @insert k s hk ih =>
    rw [word_insert s k hk, firstRatio_translate hf h, ih, Finset.prod_insert hk]
    simp only [mixedCoefficient]
    ring

/-- The insertion recurrence used to reconstruct the full-support normal form. -/
theorem value_insert {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : ThirdTrivial f) (j : Fin n)
    (s : Finset (Fin n)) (hj : j ∉ s) :
    f (word (insert j s)) = f (word s) * linearCoefficient f j *
      ∏ k ∈ s, mixedCoefficient f j k := by
  rw [word_insert s j hj]
  have hh := (div_eq_iff (hf (word s))).mp (firstRatio_word hf h j s)
  linear_combination hh

/-- Evaluating the source quadratic on a support set removes exactly the zero bits. -/
theorem quadratic_eval_word (Q : QuadraticPhase n) (s : Finset (Fin n)) :
    Q.eval (word s) = Q.constant + (∑ j ∈ s, Q.linear j) +
      ∑ j ∈ s, ∑ k ∈ s, if j < k then Q.mixed j k else 0 := by
  classical
  have hl (j : Fin n) : Q.linear j * bitValue (ZMod 4) (word s j) =
      if j ∈ s then Q.linear j else 0 := by
    by_cases hj : j ∈ s <;> simp [word, bitValue, hj]
  have hm (j k : Fin n) :
      (if j < k then Q.mixed j k * bitValue (ZMod 4) (word s j) *
        bitValue (ZMod 4) (word s k) else 0) =
      if j ∈ s then if k ∈ s then (if j < k then Q.mixed j k else 0) else 0 else 0 := by
    by_cases hj : j ∈ s <;> by_cases hk : k ∈ s <;>
      by_cases hjk : j < k <;> simp [word, bitValue, hj, hk, hjk]
  simp only [QuadraticPhase.eval, hl, hm]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.sum_filter]
  simp

theorem quadratic_eval_insert_max (Q : QuadraticPhase n) (s : Finset (Fin n))
    (j : Fin n) (hj : j ∉ s) (hmax : ∀ k ∈ s, k < j) :
    Q.eval (word (insert j s)) = Q.eval (word s) + Q.linear j +
      ∑ k ∈ s, Q.mixed k j := by
  classical
  have hnew : (∑ k ∈ s, if j < k then Q.mixed j k else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [not_lt_of_ge (le_of_lt (hmax k hk))]
  have hold (k : Fin n) (hk : k ∈ s) :
      (∑ l ∈ insert j s, if k < l then Q.mixed k l else 0) =
      Q.mixed k j + ∑ l ∈ s, if k < l then Q.mixed k l else 0 := by
    rw [Finset.sum_insert hj, ite_eq_left (hmax k hk)]
  rw [quadratic_eval_word, quadratic_eval_word, Finset.sum_insert hj,
    Finset.sum_insert hj, Finset.sum_insert hj]
  simp only [lt_self_iff_false, ite_false, zero_add, hnew]
  rw [Finset.sum_congr rfl hold, Finset.sum_add_distrib]
  abel

/-- The source's converse, including an actual `ZMod 4` quadratic witness. -/
theorem affine_of_thirdTrivial {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : ThirdTrivial f) : Affine f := by
  classical
  have ha : ∀ j : Fin n, ∃ q : ZMod 4, fourthRootPhase q = linearCoefficient f j := by
    intro j
    exact fourthRootPhase_surjective_of_pow_four (normalized_pow_four hf h (basis j))
  choose a ha using ha
  have hb : ∀ j k : Fin n, ∃ q : ZMod 4,
      (q = 0 ∨ q = 2) ∧ fourthRootPhase q = mixedCoefficient f j k := by
    intro j k
    exact evenPhase_of_sq_eq_one (secondRatio_sq hf h (basis j) (basis k))
  choose b hb hphase using hb
  let Q : QuadraticPhase n := ⟨0, a, b, fun j k _ => hb j k⟩
  have hv (s : Finset (Fin n)) : f (word s) =
      f (origin n) * fourthRootPhase (Q.eval (word s)) := by
    induction s using Finset.induction_on_max with
    | empty => rw [quadratic_eval_word]; simp [Q]
    | insert j s hmax ih =>
      have hj : j ∉ s := by
        intro hj
        exact (lt_irrefl j) (hmax j hj)
      rw [value_insert hf h j s hj, ih, quadratic_eval_insert_max Q s j hj hmax,
        fourthRootPhase_add, fourthRootPhase_add, fourthRootPhase_sum]
      change _ = f (origin n) *
        (fourthRootPhase (Q.eval (word s)) * fourthRootPhase (a j) *
        ∏ k ∈ s, fourthRootPhase (b k j))
      simp_rw [ha, hphase, mixedCoefficient_comm f _ j]
      ring
  right
  refine ⟨f (origin n), hf _, AffineSystem.unconstrained n, Q, ?_⟩
  funext x
  let s : Finset (Fin n) := Finset.univ.filter (fun j => x j = true)
  have hs : word s = x := by
    funext j
    simp [word, s]
  simpa [affineFormula, hs] using hv s

/-- The additive counterpart of the eight-term multiplicative difference. -/
def thirdDifference (q : Word n → ZMod 4) (z u v w : Word n) : ZMod 4 :=
  q (xor (xor (xor z u) v) w) + q (xor z u) + q (xor z v) + q (xor z w) -
    q (xor (xor z u) v) - q (xor (xor z u) w) - q (xor (xor z v) w) - q z

theorem thirdDifference_const (a : ZMod 4) (z u v w : Word n) :
    thirdDifference (fun _ => a) z u v w = 0 := by
  unfold thirdDifference
  abel

private theorem eight_term_add (a b c d e f g h A B C D E F G H : ZMod 4) :
    (a + A) + (b + B) + (c + C) + (d + D) - (e + E) - (f + F) -
      (g + G) - (h + H) =
    (a + b + c + d - e - f - g - h) + (A + B + C + D - E - F - G - H) := by
  ring

theorem thirdDifference_add (p q : Word n → ZMod 4) (z u v w : Word n) :
    thirdDifference (fun x => p x + q x) z u v w =
      thirdDifference p z u v w + thirdDifference q z u v w := by
  exact eight_term_add _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem thirdDifference_mul_const (a : ZMod 4) (q : Word n → ZMod 4)
    (z u v w : Word n) :
    thirdDifference (fun x => a * q x) z u v w = a * thirdDifference q z u v w := by
  unfold thirdDifference
  ring

theorem thirdDifference_sum {ι : Type*} (s : Finset ι) (q : ι → Word n → ZMod 4)
    (z u v w : Word n) :
    thirdDifference (fun x => ∑ j ∈ s, q j x) z u v w =
      ∑ j ∈ s, thirdDifference (q j) z u v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thirdDifference_const]
  | insert j s hj ih => simp [Finset.sum_insert hj, thirdDifference_add, ih]

/-- A bit has additive degree at most two modulo four, even with repeated directions. -/
theorem thirdDifference_bit (j : Fin n) (z u v w : Word n) :
    thirdDifference (fun x => bitValue (ZMod 4) (x j)) z u v w = 0 := by
  simp only [thirdDifference, xor_apply]
  cases z j <;> cases u j <;> cases v j <;> cases w j <;> decide

/-- Twice a product of bits has additive degree at most two modulo four. -/
theorem thirdDifference_even_pair (j k : Fin n) (z u v w : Word n) :
    thirdDifference (fun x => (2 : ZMod 4) * bitValue (ZMod 4) (x j) *
      bitValue (ZMod 4) (x k)) z u v w = 0 := by
  simp only [thirdDifference, xor_apply]
  cases z j <;> cases u j <;> cases v j <;> cases w j <;>
    cases z k <;> cases u k <;> cases v k <;> cases w k <;> decide

/-- Each genuine source quadratic has identically zero additive third difference. -/
theorem quadratic_thirdDifference (Q : QuadraticPhase n) (z u v w : Word n) :
    thirdDifference Q.eval z u v w = 0 := by
  unfold QuadraticPhase.eval
  rw [thirdDifference_add, thirdDifference_add, thirdDifference_const]
  simp only [zero_add]
  rw [thirdDifference_sum, thirdDifference_sum]
  have hl : (∑ j : Fin n, thirdDifference
      (fun x => Q.linear j * bitValue (ZMod 4) (x j)) z u v w) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [thirdDifference_mul_const, thirdDifference_bit, mul_zero]
  rw [hl, zero_add]
  apply Finset.sum_eq_zero
  intro j _
  rw [thirdDifference_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hjk : j < k
  · simp only [ite_eq_left hjk]
    rcases Q.even_mixed j k hjk with hq | hq
    · simp [hq, thirdDifference_const]
    · simpa only [hq] using thirdDifference_even_pair j k z u v w
  · simp [hjk, thirdDifference_const]

/-- Exponentiating the additive cancellation gives the required phase cancellation. -/
theorem quadratic_phase_cross (Q : QuadraticPhase n) (z u v w : Word n) :
    fourthRootPhase (Q.eval (xor (xor (xor z u) v) w)) *
        fourthRootPhase (Q.eval (xor z u)) * fourthRootPhase (Q.eval (xor z v)) *
        fourthRootPhase (Q.eval (xor z w)) =
      fourthRootPhase (Q.eval (xor (xor z u) v)) *
        fourthRootPhase (Q.eval (xor (xor z u) w)) *
        fourthRootPhase (Q.eval (xor (xor z v) w)) * fourthRootPhase (Q.eval z) := by
  have hh := quadratic_thirdDifference Q z u v w
  have he : Q.eval (xor (xor (xor z u) v) w) + Q.eval (xor z u) +
      Q.eval (xor z v) + Q.eval (xor z w) = Q.eval (xor (xor z u) v) +
      Q.eval (xor (xor z u) w) + Q.eval (xor (xor z v) w) + Q.eval z := by
    apply sub_eq_zero.mp
    simpa only [thirdDifference, sub_add_eq_sub_sub] using hh
  simpa only [fourthRootPhase_add] using congrArg fourthRootPhase he

/-- Nowhere-zero members of the actual affine class satisfy the third-ratio test. -/
theorem thirdTrivial_of_affine {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : Affine f) : ThirdTrivial f := by
  rcases h with rfl | ⟨s, hs, S, Q, rfl⟩
  · exact False.elim (hf (origin n) rfl)
  · have hS : ∀ x, S.Holds x := by
      intro x
      by_contra hn
      exact hf x (by simp [affineFormula, hn])
    intro z u v w
    apply (thirdRatio_eq_one_iff hf z u v w).mpr
    simp only [affineFormula, hS, ite_true]
    have hc := quadratic_phase_cross Q z u v w
    linear_combination s ^ 4 * hc

/-- Manuscript Lemma 2.6, including nullary signatures and repeated directions. -/
theorem affine_iff_thirdRatio_eq_one {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) :
    Affine f ↔ ∀ z u v w : Word n, thirdRatio f z u v w = 1 :=
  ⟨thirdTrivial_of_affine hf, affine_of_thirdTrivial hf⟩

end AffinePhase

/-- Manuscript `lem:affine-phase-criterion`, with the ratio displayed in full.
All additions in the eight arguments are coordinatewise Boolean XOR. -/
theorem affine_phase_criterion {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) :
    Affine f ↔ ∀ z u v w : Fin n → Bool,
      (f (AffinePhase.xor (AffinePhase.xor (AffinePhase.xor z u) v) w) *
        f (AffinePhase.xor z u) * f (AffinePhase.xor z v) * f (AffinePhase.xor z w)) /
      (f (AffinePhase.xor (AffinePhase.xor z u) v) *
        f (AffinePhase.xor (AffinePhase.xor z u) w) *
        f (AffinePhase.xor (AffinePhase.xor z v) w) * f z) = 1 :=
  AffinePhase.affine_iff_thirdRatio_eq_one hf

end
end Holant.Tractable
