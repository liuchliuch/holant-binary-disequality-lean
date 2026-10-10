import Holant.Proofs.AlgebraicRecognition.Enumeration
import Holant.Algebraic.FixedField
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Find


namespace Holant.LocalDrafts.EffectiveAlgebraic.FixedSystem
open Holant.Algebraic
open scoped BigOperators

abbrev Vector (d : ℕ) := Fin d → ℚ
abbrev Tuple (d n : ℕ) := Fin n → Vector d
abbrev Term (d n : ℕ) := Vector d × (Fin n → ℕ)
abbrev Equation (d n : ℕ) := List (Term d n)
abbrev System (d n : ℕ) := List (Equation d n)

def powerCode {d : ℕ} (D : ArithmeticData d) (v : Vector d) : ℕ → Vector d
  | 0 => D.unitCode
  | k + 1 => D.mulCode (powerCode D v k) v

def productCode {d : ℕ} (D : ArithmeticData d) :
    (n : ℕ) → Tuple d n → Vector d
  | 0, _ => D.unitCode
  | n + 1, v => D.mulCode (v 0) (productCode D n (Fin.tail v))

def evalTerm {d n : ℕ} (D : ArithmeticData d) (x : Tuple d n)
    (t : Term d n) : Vector d :=
  D.mulCode t.1 (productCode D n (fun i => powerCode D (x i) (t.2 i)))

def evalEquation {d n : ℕ} (D : ArithmeticData d) (x : Tuple d n) :
    Equation d n → Vector d
  | [] => 0
  | t :: ts => evalTerm D x t + evalEquation D x ts

/-- Decidable rational-coordinate equality, never classical complex equality. -/
def checkSystem {d n : ℕ} (D : ArithmeticData d) (S : System d n)
    (x : Tuple d n) : Bool :=
  S.all (fun e => decide (∀ j, evalEquation D x e j = 0))

section Semantics
variable {K : Type*} [Field K] [Algebra ℚ K] {d n : ℕ}
variable (F : FixedField K d)

noncomputable def termPolynomial (t : Term d n) : MvPolynomial (Fin n) K :=
  MvPolynomial.C (F.decode t.1) * ∏ i, MvPolynomial.X i ^ t.2 i

noncomputable def equationPolynomial (F : FixedField K d) :
    Equation d n → MvPolynomial (Fin n) K
  | [] => 0
  | t :: ts => termPolynomial F t + equationPolynomial F ts

@[simp] theorem equationPolynomial_append (a b : Equation d n) :
    equationPolynomial F (a ++ b) = equationPolynomial F a + equationPolynomial F b := by
  induction a with
  | nil => simp [equationPolynomial]
  | cons t ts ih => simp [equationPolynomial, ih, add_assoc]

/-- Every actual finite-dimensional polynomial has sparse coefficient data.
This is a representation theorem, not an executable conversion of abstract K
elements to rational coordinates. Encoded coefficients must be supplied as input. -/
theorem exists_equation (p : MvPolynomial (Fin n) K) :
    ∃ e : Equation d n, equationPolynomial F e = p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨[(F.decode.symm a, fun i => u i)], ?_⟩
    simp only [equationPolynomial, termPolynomial, LinearEquiv.apply_symm_apply,
      add_zero, MvPolynomial.monomial_eq]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a ++ b, equationPolynomial_append F a b⟩

def IsSolution (S : System d n) (x : Fin n → K) : Prop :=
  ∀ e ∈ S, MvPolynomial.aeval x (equationPolynomial F e) = 0

@[simp] theorem decode_powerCode (v : Vector d) (k : ℕ) :
    F.decode (powerCode F.toArithmeticData v k) = (F.decode v) ^ k := by
  induction k with
  | zero =>
    change F.decode F.unitCode = (F.decode v) ^ 0
    rw [pow_zero]
    exact F.decode_unit
  | succ k ih =>
    change F.decode (F.mulCode (powerCode F.toArithmeticData v k) v) = _
    rw [F.decode_mul, ih, pow_succ]

@[simp] theorem decode_productCode (n : ℕ) (v : Tuple d n) :
    F.decode (productCode F.toArithmeticData n v) = ∏ i, F.decode (v i) := by
  induction n with
  | zero => simpa [productCode] using F.decode_unit
  | succ n ih =>
    change F.decode (F.mulCode (v 0) (productCode F.toArithmeticData n (Fin.tail v))) = _
    rw [F.decode_mul, ih, Fin.prod_univ_succ]
    rfl

@[simp] theorem decode_evalTerm (x : Tuple d n) (t : Term d n) :
    F.decode (evalTerm F.toArithmeticData x t) =
      MvPolynomial.aeval (fun i => F.decode (x i)) (termPolynomial F t) := by
  change F.decode (F.mulCode t.1 _) = _
  rw [F.decode_mul, decode_productCode]
  simp [termPolynomial, decode_powerCode]

@[simp] theorem decode_evalEquation (x : Tuple d n) (e : Equation d n) :
    F.decode (evalEquation F.toArithmeticData x e) =
      MvPolynomial.aeval (fun i => F.decode (x i)) (equationPolynomial F e) := by
  induction e with
  | nil => simp [evalEquation, equationPolynomial]
  | cons t ts ih => simp [evalEquation, equationPolynomial, ih]

theorem checkSystem_iff (S : System d n) (x : Tuple d n) :
    checkSystem F.toArithmeticData S x = true ↔
      IsSolution F S (fun i => F.decode (x i)) := by
  have hz (e : Equation d n) :
      (∀ j, evalEquation F.toArithmeticData x e j = 0) ↔
        MvPolynomial.aeval (fun i => F.decode (x i)) (equationPolynomial F e) = 0 := by
    rw [← decode_evalEquation]
    constructor
    · intro h
      have he : evalEquation F.toArithmeticData x e = 0 := funext h
      rw [he, map_zero]
    · intro h
      have he : evalEquation F.toArithmeticData x e = 0 :=
        F.decode.injective (h.trans (F.decode.map_zero).symm)
      intro j
      exact congrFun he j
  simp only [checkSystem, List.all_eq_true, decide_eq_true_eq, IsSolution, hz]

end Semantics

/-- Inspect one code, rejecting either malformed data or a failed equation. -/
def candidate {d n : ℕ} (D : ArithmeticData d) (S : System d n)
    (k : ℕ) : Option (Tuple d n) := do
  let x ← tupleAt n k
  if checkSystem D S x then some x else none

theorem candidate_some_iff {d n : ℕ} (D : ArithmeticData d) (S : System d n)
    (k : ℕ) (x : Tuple d n) :
    candidate D S k = some x ↔
      tupleAt n k = some x ∧ checkSystem D S x = true := by
  unfold candidate
  cases h : (tupleAt n k : Option (Tuple d n)) with
  | none => simp
  | some y =>
    cases ht : checkSystem D S y <;> simp_all
    all_goals
      intro hyx
      subst x
      exact ht

theorem candidate_exists {K : Type*} [Field K] [Algebra ℚ K] {d n : ℕ}
    (F : FixedField K d) (S : System d n)
    (h : ∃ x : Fin n → K, IsSolution F S x) :
    ∃ k, (candidate F.toArithmeticData S k).isSome = true := by
  obtain ⟨x, hx⟩ := h
  let v : Tuple d n := fun i => F.decode.symm (x i)
  have hv : checkSystem F.toArithmeticData S v = true := by
    apply (checkSystem_iff F S v).mpr
    simpa [v] using hx
  have hc := (candidate_some_iff F.toArithmeticData S (Encodable.encode v) v).mpr
    ⟨tupleAt_encode v, hv⟩
  exact ⟨Encodable.encode v, by rw [hc]; rfl⟩

/-- Nat.find performs sequential decidable search. Nonemptiness is used only
in its well-founded termination proof, not to choose a runtime witness. -/
def searchIndex {K : Type*} [Field K] [Algebra ℚ K] {d n : ℕ}
    (D : ArithmeticData d) (F : FixedField K d) (hD : F.toArithmeticData = D)
    (S : System d n) (h : ∃ x : Fin n → K, IsSolution F S x) : ℕ :=
  Nat.find (show ∃ k, (candidate D S k).isSome = true by
    simpa only [← hD] using candidate_exists F S h)

theorem searchIndex_spec {K : Type*} [Field K] [Algebra ℚ K] {d n : ℕ}
    (D : ArithmeticData d) (F : FixedField K d) (hD : F.toArithmeticData = D)
    (S : System d n) (h : ∃ x : Fin n → K, IsSolution F S x) :
    (candidate D S (searchIndex D F hD S h)).isSome = true := by
  have hterm : ∃ k, (candidate D S k).isSome = true := by
    simpa only [← hD] using candidate_exists F S h
  change (candidate D S (Nat.find hterm)).isSome = true
  exact Nat.find_spec hterm

/-- The returned vectors are actual rational data. F is used only by the proof
argument of searchIndex; no semantic basis is evaluated by the search. -/
def search {K : Type*} [Field K] [Algebra ℚ K] {d n : ℕ}
    (D : ArithmeticData d) (F : FixedField K d) (hD : F.toArithmeticData = D)
    (S : System d n) (h : ∃ x : Fin n → K, IsSolution F S x) : Tuple d n :=
  (candidate D S (searchIndex D F hD S h)).get
    (searchIndex_spec D F hD S h)

theorem search_correct {K : Type*} [Field K] [Algebra ℚ K] {d n : ℕ}
    (D : ArithmeticData d) (F : FixedField K d) (hD : F.toArithmeticData = D)
    (S : System d n) (h : ∃ x : Fin n → K, IsSolution F S x) :
    IsSolution F S (fun i => F.decode (search D F hD S h i)) := by
  have hc : candidate D S (searchIndex D F hD S h) = some (search D F hD S h) := by
    simp only [search, Option.some_get]
  have ht := ((candidate_some_iff D S _ _).mp hc).2
  apply (checkSystem_iff F S _).mp
  simpa only [hD] using ht

/-- The sequential search stops no later than the code of any satisfying tuple. -/
theorem searchIndex_le {K : Type*} [Field K] [Algebra ℚ K] {d n : ℕ}
    (D : ArithmeticData d) (F : FixedField K d) (hD : F.toArithmeticData = D)
    (S : System d n) (h : ∃ x : Fin n → K, IsSolution F S x)
    (v : Tuple d n) (hv : checkSystem D S v = true) :
    searchIndex D F hD S h ≤ Encodable.encode v := by
  apply Nat.find_min'
  have hc := (candidate_some_iff D S (Encodable.encode v) v).mpr
    ⟨tupleAt_encode v, hv⟩
  rw [hc]
  rfl

end Holant.LocalDrafts.EffectiveAlgebraic.FixedSystem
