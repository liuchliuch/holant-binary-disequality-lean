import Holant.Proofs.Recognition.PolynomialDecision
import Holant.Proofs.Recognition.TensorDecisionCleared

/-!
# Literal polynomial systems for finite tensor-recognition branches

The input-table expressions and all port addresses are finite syntax. Each
branch has exactly one existential coordinate, the inverse of its tested pivot.
All other equations are denominator-cleared input-table equalities and, for
matching, zero constraints on specified entries. There are no selected factors,
transformed RootCodes, desired answers, or evaluator callbacks in the syntax.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorDecisionSyntax

open Holant.Tractable PolynomialDecision TensorDecisionNormalization TensorDecisionCleared
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open scoped BigOperators

variable {m n : ℕ}

/-- Preserve the exact input bindings while adding one inverse coordinate. -/
def lift (e : Expr m) : Expr (m+1) := Expr.rename (Fin.castAdd 1) e

def difference (a b : Expr m) : Expr m := .add a (.neg b)

def row (table : (Fin n → Bool) → Expr m) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot x : Fin n → Bool) : Expr m :=
  difference
    (.mul (table pivot) (Expr.product (List.ofFn (fun i =>
      table (blockWord count arity ports pivot i (fun j => x (ports ⟨i,j⟩)))))))
    (.mul (table x) (Expr.power (table pivot) count))

def rows (table : (Fin n → Bool) → Expr m) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool) : List (Expr m) :=
  (SparseTransform.allWords n).map (row table count arity ports pivot)

def support (table : (Fin n → Bool) → Expr m) (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool) : List (Expr m) :=
  (List.finRange count).flatMap (fun i =>
    ((SparseTransform.allWords (arity i)).filter (fun y => decide (1 < Holant.weight y))).map
      (fun y => table (blockWord count arity ports pivot i y)))

def guard (table : (Fin n → Bool) → Expr m) (pivot : Fin n → Bool) : Expr (m+1) :=
  difference (.mul (lift (table pivot)) (.variable (Fin.natAdd m 0))) (.constant 1)

/-- Every branch is a concrete finite rational-polynomial list. -/
def branch (oneHot : Bool) (table : (Fin n → Bool) → Expr m) (count : ℕ)
    (arity : Fin count → ℕ) (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) : List (Expr (m+1)) :=
  guard table pivot :: ((rows table count arity ports pivot ++
    if oneHot then support table count arity ports pivot else []).map lift)

/-- Semantic branch condition, consisting only of the original finite table constraints. -/
def BranchTest {K : Type*} [Field K] (oneHot : Bool) (f : Signature K n) (count : ℕ)
    (arity : Fin count → ℕ) (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n)
    (pivot : Fin n → Bool) : Prop :=
  f pivot ≠ 0 ∧ Rows f count arity ports pivot ∧
    (oneHot = true → ∀ i y, 1 < Holant.weight y → f (blockWord count arity ports pivot i y) = 0)

section Evaluation
variable {E : Type} [Field E] [Algebra ℚ E]

theorem lift_eval (e : Expr m) (w : Fin m → E) (u : Fin 1 → E) :
    (lift e).eval (Fin.addCases w u) = e.eval w := by
  rw [lift, Expr.eval_rename]
  simp only [Fin.addCases_left]

theorem row_eval (table : (Fin n → Bool) → Expr m) (w : Fin m → E)
    (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot x : Fin n → Bool) :
    (row table count arity ports pivot x).eval w =
      (table pivot).eval w * sliceProduct (fun y => (table y).eval w) count arity ports pivot x -
        (table x).eval w * ((table pivot).eval w) ^ count := by
  simp only [row,difference,Expr.eval,Expr.eval_product,Expr.eval_power,List.map_ofFn,
    List.prod_ofFn,sliceProduct,sub_eq_add_neg,Function.comp_def]

theorem rows_eval_iff (table : (Fin n → Bool) → Expr m) (w : Fin m → E)
    (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool) :
    (∀ e ∈ rows table count arity ports pivot, e.eval w = 0) ↔
      Rows (fun x => (table x).eval w) count arity ports pivot := by
  simp only [rows,List.forall_mem_map,SparseTransform.mem_allWords,forall_true_left,
    row_eval,sub_eq_zero,Rows]

theorem support_eval_iff (table : (Fin n → Bool) → Expr m) (w : Fin m → E)
    (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool) :
    (∀ e ∈ support table count arity ports pivot, e.eval w = 0) ↔
      ∀ i y, 1 < Holant.weight y → (table (blockWord count arity ports pivot i y)).eval w = 0 := by
  simp only [support,List.forall_mem_flatMap,List.mem_finRange,forall_true_left,
    List.forall_mem_map,List.mem_filter,SparseTransform.mem_allWords,true_and,
    decide_eq_true_eq]

theorem branch_eval_iff (oneHot : Bool) (table : (Fin n → Bool) → Expr m) (w : Fin m → E)
    (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool)
    (u : Fin 1 → E) :
    (∀ e ∈ branch oneHot table count arity ports pivot, e.eval (Fin.addCases w u) = 0) ↔
      (table pivot).eval w * u 0 = 1 ∧
      Rows (fun x => (table x).eval w) count arity ports pivot ∧
      (oneHot = true → ∀ i y, 1 < Holant.weight y →
        (table (blockWord count arity ports pivot i y)).eval w = 0) := by
  simp only [branch,List.forall_mem_cons,List.forall_mem_map,lift_eval,
    List.forall_mem_append,rows_eval_iff]
  have hg : (guard table pivot).eval (Fin.addCases w u) = 0 ↔
      (table pivot).eval w * u 0 = 1 := by
    simp only [guard,difference,Expr.eval,lift_eval,Fin.addCases_right,map_one,
      ←sub_eq_add_neg,sub_eq_zero]
  rw [hg]
  cases oneHot <;> simp [support_eval_iff]

/-- The inverse coordinate is an actual algebraic nonzero guard, and has a
solution exactly for accepted finite structural branches. -/
theorem branch_solutions_iff (oneHot : Bool) (table : (Fin n → Bool) → Expr m) (w : Fin m → E)
    (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool) :
    (∃ u : Fin 1 → E,
      ∀ e ∈ branch oneHot table count arity ports pivot, e.eval (Fin.addCases w u) = 0) ↔
      BranchTest oneHot (fun x => (table x).eval w) count arity ports pivot := by
  simp only [branch_eval_iff]
  constructor
  · rintro ⟨u,hp,hr,hs⟩
    exact ⟨left_ne_zero_of_mul_eq_one hp,hr,hs⟩
  · rintro ⟨hp,hr,hs⟩
    exact ⟨fun _ => ((table pivot).eval w)⁻¹,mul_inv_cancel₀ hp,hr,hs⟩
end Evaluation

theorem arityTwo_branch_iff {K : Type*} [Field K] (f : Signature K n)
    (S : TensorDecision.Shape n) (pivot : Fin n → Bool) :
    BranchTest false f S.count S.arity S.ports pivot ↔ ArityTwoAccepts f S pivot := by
  simp [BranchTest,ArityTwoAccepts]

theorem oneHot_branch_iff {K : Type*} [Field K] (f : Signature K n)
    (S : TensorDecisionStable.Shape n) (pivot : Fin n → Bool) :
    BranchTest true f S.count S.arity S.ports pivot ↔ OneHotAccepts f S pivot := by
  simp only [BranchTest,OneHotAccepts,true_implies]
  tauto

theorem branchTest_map_iff {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (hφ : Function.Injective φ) (oneHot : Bool) (f : Signature K n)
    (count : ℕ) (arity : Fin count → ℕ)
    (ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n) (pivot : Fin n → Bool) :
    BranchTest oneHot (fun x => φ (f x)) count arity ports pivot ↔
      BranchTest oneHot f count arity ports pivot := by
  simp only [BranchTest,Rows,sliceProduct,ne_eq,map_eq_zero_iff φ hφ]
  simp only [←map_prod,←map_mul,←map_pow,hφ.eq_iff]

end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorDecisionSyntax
