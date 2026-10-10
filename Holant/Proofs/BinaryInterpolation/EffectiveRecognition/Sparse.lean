import Holant.Algebraic.FixedFieldInverse
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Order.WellQuasiOrder


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse

open Holant.Algebraic MvPolynomial
open scoped BigOperators

abbrev Exponent (v : ℕ) := Fin v → ℕ
abbrev Coefficient (d : ℕ) := Fin d → ℚ
abbrev Term (v d : ℕ) := Exponent v × Coefficient d
abbrev Poly (v d : ℕ) := List (Term v d)

def coefficient {v d : ℕ} (p : Poly v d) (a : Exponent v) : Coefficient d :=
  ((p.filter (fun t => decide (t.1 = a))).map Prod.snd).sum
def add {v d : ℕ} (p q : Poly v d) : Poly v d := p ++ q
def neg {v d : ℕ} (p : Poly v d) : Poly v d := p.map (fun t => (t.1, -t.2))
def sub {v d : ℕ} (p q : Poly v d) : Poly v d := add p (neg q)
def termMul {v d : ℕ} (D : ArithmeticData d) (t : Term v d) (p : Poly v d) : Poly v d :=
  p.map (fun u => (t.1 + u.1, D.mulCode t.2 u.2))
def mul {v d : ℕ} (D : ArithmeticData d) (p q : Poly v d) : Poly v d :=
  p.flatMap (fun t => termMul D t q)
def one {v d : ℕ} (D : ArithmeticData d) : Poly v d := [(0, D.unitCode)]

def less {v : ℕ} (a b : Exponent v) : Bool :=
  decide (∃ i : Fin v, (∀ j : Fin v, j < i → a j = b j) ∧ a i < b i)
def divides {v : ℕ} (a b : Exponent v) : Bool := decide (∀ i, a i ≤ b i)

/-- Highest live key. The candidate list is literal input support, not a
chosen mathematical support enumeration. -/
def select {v d : ℕ} (p : Poly v d) : List (Exponent v) → Option (Exponent v)
  | [] => none
  | a :: as =>
    if coefficient p a = 0 then select p as else
      match select p as with
      | none => some a
      | some b => some (if less a b then b else a)
def leading {v d : ℕ} (p : Poly v d) : Option (Term v d) :=
  (select p (p.map Prod.fst)).map (fun a => (a, coefficient p a))
def isZero {v d : ℕ} (p : Poly v d) : Bool := (leading p).isNone

noncomputable def exponent {v : ℕ} (a : Exponent v) : Fin v →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponent_apply {v : ℕ} (a : Exponent v) (i : Fin v) : exponent a i = a i := rfl
theorem exponent_injective {v : ℕ} : Function.Injective (exponent (v := v)) := by
  intro a b h; funext i; exact congrArg (fun x => x i) h
@[simp] theorem exponent_eq {v : ℕ} (a b : Exponent v) : exponent a = exponent b ↔ a = b :=
  exponent_injective.eq_iff
@[simp] theorem exponent_add {v : ℕ} (a b : Exponent v) : exponent (a + b) = exponent a + exponent b := by ext i; rfl
@[simp] theorem exponent_sub {v : ℕ} (a b : Exponent v) : exponent (a - b) = exponent a - exponent b := by ext i; rfl
@[simp] theorem exponent_zero {v : ℕ} : exponent (0 : Exponent v) = 0 := by ext i; rfl
@[simp] theorem exponent_coe {v : ℕ} (a : Fin v →₀ ℕ) : exponent (fun i => a i) = a := by ext i; rfl

noncomputable def order (v : ℕ) : MonomialOrder (Fin v) := MonomialOrder.lex

theorem less_exact {v : ℕ} (a b : Exponent v) :
    less a b = true ↔ (order v).toSyn (exponent a) < (order v).toSyn (exponent b) := by
  simp only [less, decide_eq_true_eq]
  rfl

variable {K : Type*} [Field K] [Algebra ℚ K] {v d : ℕ} (F : FixedField K d)

noncomputable def denote (p : Poly v d) : MvPolynomial (Fin v) K :=
  (p.map (fun t => monomial (exponent t.1) (F.decode t.2))).sum

@[simp] theorem denote_nil : denote F ([] : Poly v d) = 0 := rfl
@[simp] theorem denote_cons (t : Term v d) (p : Poly v d) :
    denote F (t :: p) = monomial (exponent t.1) (F.decode t.2) + denote F p := rfl
@[simp] theorem denote_add (p q : Poly v d) : denote F (add p q) = denote F p + denote F q := by
  simp [denote, add]
@[simp] theorem denote_neg (p : Poly v d) : denote F (neg p) = -denote F p := by
  induction p with
  | nil => simp [neg]
  | cons t p ih =>
    change monomial (exponent t.1) (F.decode (-t.2)) + denote F (neg p) = _
    rw [map_neg, map_neg, ih, denote_cons, neg_add]
@[simp] theorem denote_sub (p q : Poly v d) : denote F (sub p q) = denote F p - denote F q := by
  simp [sub, sub_eq_add_neg]
@[simp] theorem denote_termMul (t : Term v d) (p : Poly v d) :
    denote F (termMul F.toArithmeticData t p) =
      monomial (exponent t.1) (F.decode t.2) * denote F p := by
  induction p with
  | nil => simp [termMul]
  | cons u p ih =>
    simp only [termMul, List.map_cons, denote_cons] at *
    rw [ih, exponent_add, ← FixedField.mulCode, F.decode_mul, mul_add, monomial_mul_monomial]

@[simp] theorem denote_mul (p q : Poly v d) :
    denote F (mul F.toArithmeticData p q) = denote F p * denote F q := by
  induction p with
  | nil => simp [mul]
  | cons t p ih =>
    change denote F (add (termMul F.toArithmeticData t q) (mul F.toArithmeticData p q)) = _
    rw [denote_add, denote_termMul, ih, denote_cons, add_mul]

@[simp] theorem denote_one : denote F (one (v := v) F.toArithmeticData) = 1 := by
  simp [one]

@[simp] theorem coefficient_nil (a : Exponent v) : coefficient ([] : Poly v d) a = 0 := rfl
theorem coefficient_cons (t : Term v d) (p : Poly v d) (a : Exponent v) :
    coefficient (t :: p) a = (if t.1 = a then t.2 else 0) + coefficient p a := by
  by_cases h : t.1 = a <;> simp [coefficient, h]

theorem coefficient_exact (p : Poly v d) (a : Exponent v) :
    (denote F p).coeff (exponent a) = F.decode (coefficient p a) := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [denote_cons, MvPolynomial.coeff_add, ih, coefficient_cons, map_add]
    by_cases h : t.1 = a <;> simp [coeff_monomial, h, exponent_eq]

theorem coefficient_eq_zero_iff (p : Poly v d) (a : Exponent v) :
    (denote F p).coeff (exponent a) = 0 ↔ coefficient p a = 0 := by
  rw [coefficient_exact, ← map_zero F.decode]
  exact F.decode.injective.eq_iff

theorem coefficient_of_not_mem (p : Poly v d) (a : Exponent v)
    (h : a ∉ p.map Prod.fst) : coefficient p a = 0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    have ht : t.1 ≠ a := by intro he; apply h; simp [he]
    have hp : a ∉ p.map Prod.fst := fun ha => h (by simp [ha])
    simp [coefficient_cons, ht, ih hp]

theorem coefficient_live_mem (p : Poly v d) (a : Exponent v) (h : coefficient p a ≠ 0) :
    a ∈ p.map Prod.fst := by
  by_contra hn
  exact h (coefficient_of_not_mem p a hn)

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
