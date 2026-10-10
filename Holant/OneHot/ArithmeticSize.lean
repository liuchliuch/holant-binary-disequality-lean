import Holant.OneHot.ClosedTree
import Holant.Algebraic.FixedFamilySize

/-!
# Executed arithmetic traces and bounded sum-product certificates

`Arithmetic.values` records the actual operands and result of every instruction,
following exactly the continuation selected by `run`. Sum-product certificates
control polynomial degree and the logarithm of the summand count separately from
instruction count. They therefore do not assume that a short arithmetic program
has short intermediate values.
-/

namespace Holant.OneHot

open scoped BigOperators

namespace Arithmetic

variable {K A B : Type*} [CommSemiring K]

/-- All actual instruction operands/results, in execution order. Pure return
values are handled separately, since an arbitrary return type need not be `K`. -/
def values : Arithmetic K A → List K
  | .pure _ => []
  | .add x y next => x :: y :: (x + y) :: (next (x + y)).values
  | .mul x y next => x :: y :: (x * y) :: (next (x * y)).values

@[simp] theorem values_pure (a : A) : (Arithmetic.pure (K := K) a).values = [] := rfl

@[simp] theorem values_bind (p : Arithmetic K A) (f : A → Arithmetic K B) :
    (p.bind f).values = p.values ++ (f p.run.1).values := by
  induction p with
  | pure a => rfl
  | add x y next ih => simp [bind, values, run, ih]
  | mul x y next ih => simp [bind, values, run, ih]

@[simp] theorem values_addOp (x y : K) : (addOp x y).values = [x, y, x + y] := rfl
@[simp] theorem values_mulOp (x y : K) : (mulOp x y).values = [x, y, x * y] := rfl

/-- Exactly three recorded field values for every executed arithmetic instruction. -/
theorem values_length (p : Arithmetic K A) : p.values.length = 3 * p.run.2 := by
  induction p with
  | pure a => rfl
  | add x y next ih => simp [values, run, ih]; omega
  | mul x y next ih => simp [values, run, ih]; omega

/-- Every operand and result of the executed program satisfies the predicate. -/
def Safe (P : K → Prop) (p : Arithmetic K A) : Prop := ∀ x ∈ p.values, P x

theorem Safe.mono {P Q : K → Prop} {p : Arithmetic K A}
    (h : Safe P p) (hp : ∀ x, P x → Q x) : Safe Q p :=
  fun x hx => hp x (h x hx)

@[simp] theorem safe_pure (P : K → Prop) (a : A) : Safe P (.pure a) := by
  simp [Safe]

theorem safe_bind {P : K → Prop} {p : Arithmetic K A} {f : A → Arithmetic K B}
    (hp : Safe P p) (hf : Safe P (f p.run.1)) : Safe P (p.bind f) := by
  intro x hx
  rw [values_bind, List.mem_append] at hx
  exact hx.elim (hp x) (hf x)

theorem safe_addOp {P : K → Prop} {x y : K}
    (hx : P x) (hy : P y) (hz : P (x + y)) : Safe P (addOp x y) := by
  simpa [Safe, List.mem_cons, or_imp, forall_and] using And.intro hx (And.intro hy hz)

theorem safe_mulOp {P : K → Prop} {x y : K}
    (hx : P x) (hy : P y) (hz : P (x * y)) : Safe P (mulOp x y) := by
  simpa [Safe, List.mem_cons, or_imp, forall_and] using And.intro hx (And.intro hy hz)

end Arithmetic

namespace ArithmeticSize

variable {K A : Type*} [CommSemiring K]

/-- A literal sum of at most `2^b` products, each of degree exactly `b`.
The coefficient family contains a designated unit, allowing harmless padding. -/
def Bound (coeff : A → K) (b : ℕ) (x : K) : Prop :=
  ∃ L : ℕ, ∃ labels : Fin L → Fin b → A,
    L ≤ 2 ^ b ∧ x = ∑ t, ∏ i, coeff (labels t i)

namespace Bound

variable {coeff : A → K} {b c : ℕ} {x y : K}

theorem zero (_aone : A) (b : ℕ) : Bound coeff b 0 := by
  refine ⟨0, fun t => Fin.elim0 t, Nat.zero_le _, ?_⟩
  simp

theorem one : Bound coeff 0 1 := by
  refine ⟨1, fun _ => Fin.elim0, by decide, ?_⟩
  simp

theorem coefficient (a : A) : Bound coeff 1 (coeff a) := by
  refine ⟨1, fun _ _ => a, by decide, ?_⟩
  simp

/-- Padding uses only the fixed unit coefficient, never an instance-dependent
new field constant. Both the product degree and exponent budget increase. -/
theorem pad (aone : A) (hone : coeff aone = 1) (h : Bound coeff b x) (k : ℕ) :
    Bound coeff (b + k) x := by
  rcases h with ⟨L, labels, hL, hx⟩
  refine ⟨L, fun t => Fin.addCases (labels t) (fun _ => aone),
    hL.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right b k)), ?_⟩
  simpa [Fin.prod_univ_add, hone] using hx

theorem mono (aone : A) (hone : coeff aone = 1) (h : Bound coeff b x) (hbc : b ≤ c) :
    Bound coeff c x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hbc
  exact h.pad aone hone k

/-- Multiplication concatenates two disjoint product lists. The budgets add;
there is no unrestricted repeated-squaring size inference. -/
theorem mul (hx : Bound coeff b x) (hy : Bound coeff c y) : Bound coeff (b + c) (x * y) := by
  classical
  rcases hx with ⟨L, f, hL, rfl⟩
  rcases hy with ⟨M, g, hM, rfl⟩
  let en := (Fintype.equivFin (Fin L × Fin M)).symm
  refine ⟨Fintype.card (Fin L × Fin M),
    fun t => Fin.addCases (f (en t).1) (g (en t).2), ?_, ?_⟩
  · simpa [Fintype.card_prod, pow_add] using Nat.mul_le_mul hL hM
  · simp only [Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]
    rw [en.sum_comp (fun z => (∏ i, coeff (f z.1 i)) * ∏ i, coeff (g z.2 i))]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]

/-- Adding two expansions of the same budget costs one exponent bit and one
unit padding coefficient. -/
theorem add (aone : A) (hone : coeff aone = 1)
    (hx : Bound coeff b x) (hy : Bound coeff b y) : Bound coeff (b + 1) (x + y) := by
  rcases hx with ⟨L, f, hL, rfl⟩
  rcases hy with ⟨M, g, hM, rfl⟩
  refine ⟨L + M, fun t => Fin.addCases (Fin.addCases f g t) (fun _ => aone), ?_, ?_⟩
  · rw [pow_succ]
    omega
  · simp only [Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]
    rw [Fin.sum_univ_add]
    simp [hone]

end Bound

/-- The fixed-field bit bound is linear in the structural certificate budget. -/
def bitBound {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : Algebraic.FixedField K n) {A : Type*} [Fintype A]
    (coeff : A → Fin n → ℚ) (b : ℕ) : ℕ :=
  let M := F.toArithmeticData.familyBound coeff
  let D := F.toArithmeticData.familyDenominator coeff
  n * (4 * (b + M.size + b * (n * n * M * M).size + (2 * b + 1) * D.size + 3) + 1)

/-- Apply the existing exact common-denominator/numerator theorem to any actual
intermediate value with a bounded expansion. -/
theorem Bound.encoded_length_le {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : Algebraic.FixedField K n) {A : Type*} [Fintype A]
    (coeff : A → Fin n → ℚ) {b : ℕ} {x : K}
    (h : Bound (fun a => F.decode (coeff a)) b x) :
    (F.encoding.encode x).length ≤ bitBound F coeff b := by
  rcases h with ⟨L, labels, hL, rfl⟩
  exact F.sumProducts_answer_length_le_exponential coeff labels hL

end ArithmeticSize
end Holant.OneHot
