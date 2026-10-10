import Holant.Tractable.Product
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


namespace Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open Holant Holant.Tractable
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- true is equality; false is disequality. The original port indices remain. -/
abbrev Edge (n : ℕ) := (Fin n × Fin n) × Bool
abbrev Skeleton (n : ℕ) := Finset (Edge n)
abbrev Parameter (n : ℕ) := Option (Fin n × Bool)

def equalEdge {n : ℕ} (j k : Fin n) : Edge n := ((j,k),true)
def unequalEdge {n : ℕ} (j k : Fin n) : Edge n := ((j,k),false)

def reverseEdge {n : ℕ} (e : Edge n) : Edge n := ((e.1.2,e.1.1),e.2)

def edgeHolds {n : ℕ} (e : Edge n) (x : Fin n → Bool) : Prop :=
  if e.2 then x e.1.1 = x e.1.2 else x e.1.1 ≠ x e.1.2

theorem edgeHolds_reverse {n : ℕ} (e : Edge n) (x : Fin n → Bool) :
    edgeHolds (reverseEdge e) x ↔ edgeHolds e x := by
  obtain ⟨⟨j,k⟩,b⟩ := e
  cases b <;> simp [edgeHolds, reverseEdge, eq_comm]

def holds {n : ℕ} (S : Skeleton n) (x : Fin n → Bool) : Prop :=
  ∀ e ∈ S, edgeHolds e x

@[simp] theorem holds_empty {n : ℕ} (x : Fin n → Bool) : holds ∅ x := by
  simp [holds]

@[simp] theorem holds_insert {n : ℕ} (S : Skeleton n) (e : Edge n) (x : Fin n → Bool) :
    holds (insert e S) x ↔ edgeHolds e x ∧ holds S x := by
  simp [holds]

def mask {K : Type*} [Semiring K] {n : ℕ}
    (S : Skeleton n) (x : Fin n → Bool) : K := if holds S x then 1 else 0

def edgeMask {K : Type*} [Semiring K] {n : ℕ}
    (e : Edge n) (x : Fin n → Bool) : K := if edgeHolds e x then 1 else 0

def unaryWeight {K : Type*} [CommMonoid K] {n : ℕ}
    (u : Fin n → Bool → K) (x : Fin n → Bool) : K := ∏ j, u j (x j)

def evaluate {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (θ : Parameter n → K) : Signature K n := fun x =>
  θ none * mask S x * unaryWeight (fun j b => θ (some (j,b))) x

theorem mask_insert {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (e : Edge n) (x : Fin n → Bool) :
    mask (K := K) (insert e S) x = edgeMask e x * mask S x := by
  by_cases he : edgeHolds e x <;> by_cases hS : holds S x <;>
    simp [mask, edgeMask, holds_insert, he, hS]

/-- The same constraint twice is retained once, never cancelled modulo two. -/
theorem duplicate_edge {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (e : Edge n) (θ : Parameter n → K) :
    evaluate (insert e (insert e S)) θ = evaluate (insert e S) θ := by simp

/-- Ordered codes may be redundant; reversing an edge has exactly the same
constraint semantics, so no unordered-pair behavior is lost. -/
theorem reverse_edge {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (e : Edge n) (θ : Parameter n → K) :
    evaluate (insert (reverseEdge e) S) θ = evaluate (insert e S) θ := by
  funext x
  simp only [evaluate, mask_insert, edgeMask, edgeHolds_reverse]

theorem edgeMask_equal {K : Type*} [Semiring K] {n : ℕ}
    (j k : Fin n) (x : Fin n → Bool) :
    edgeMask (K := K) (equalEdge j k) x = Signature.equality (x j) (x k) := by
  simp [edgeMask, edgeHolds, equalEdge, Signature.equality]

theorem edgeMask_unequal {K : Type*} [Semiring K] {n : ℕ}
    (j k : Fin n) (x : Fin n → Bool) :
    edgeMask (K := K) (unequalEdge j k) x = Signature.disequality (x j) (x k) := by
  by_cases h : x j = x k <;>
    simp [edgeMask, edgeHolds, unequalEdge, Signature.disequality, h]

/-- Equality loops are scalar one and can be deleted. -/
theorem equality_loop {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (j : Fin n) (θ : Parameter n → K) :
    evaluate (insert (equalEdge j j) S) θ = evaluate S θ := by
  funext x
  simp [evaluate, mask_insert, edgeMask_equal, Signature.equality]

/-- A disequality loop annihilates the whole template, at every parameter value. -/
theorem disequality_loop {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (j : Fin n) (θ : Parameter n → K) :
    evaluate (insert (unequalEdge j j) S) θ = 0 := by
  funext x
  simp [evaluate, mask_insert, edgeMask_unequal, Signature.disequality]

/-- Opposite signs on the same pair force zero; they are not XORed away. -/
theorem opposite_edges {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (j k : Fin n) (θ : Parameter n → K) :
    evaluate (insert (equalEdge j k) (insert (unequalEdge j k) S)) θ = 0 := by
  funext x
  by_cases h : x j = x k <;>
    simp [evaluate, mask_insert, edgeMask_equal, edgeMask_unequal,
      Signature.equality, Signature.disequality, h]

theorem scalar_zero {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (θ : Parameter n → K) (h : θ none = 0) : evaluate S θ = 0 := by
  funext x
  simp [evaluate, h]

theorem zero_unary {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (θ : Parameter n → K) (j : Fin n)
    (h : ∀ b, θ (some (j,b)) = 0) : evaluate S θ = 0 := by
  funext x
  have hz : unaryWeight (fun i b => θ (some (i,b))) x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) (h (x j))
  simp [evaluate, hz]

theorem nullary {K : Type*} [CommSemiring K]
    (S : Skeleton 0) (θ : Parameter 0 → K) : evaluate S θ = fun _ => θ none := by
  funext x
  have h : holds S x := by intro e he; exact Fin.elim0 e.1.1
  simp [evaluate, mask, h, unaryWeight]

def allSkeletons (n : ℕ) : Finset (Skeleton n) := Finset.univ

theorem parameter_count (n : ℕ) : Fintype.card (Parameter n) = 1 + 2*n := by
  simp [Parameter, Fintype.card_option, Fintype.card_prod] <;> ring

theorem edge_count (n : ℕ) : Fintype.card (Edge n) = 2*n*n := by
  simp [Edge, Fintype.card_prod] <;> ring

theorem skeleton_count (n : ℕ) : Fintype.card (Skeleton n) = 2^(2*n*n) := by
  change Fintype.card (Finset (Edge n)) = _
  rw [Fintype.card_finset,edge_count]

theorem allSkeletons_count (n : ℕ) : (allSkeletons n).card = 2^(2*n*n) := by
  simpa only [allSkeletons, Finset.card_univ] using skeleton_count n

/-- Fixed-size coefficient formula, independent of how a template was obtained. -/
theorem entry_formula {K : Type*} [CommSemiring K] {n : ℕ}
    (S : Skeleton n) (θ : Parameter n → K) (x : Fin n → Bool) :
    evaluate S θ x = if holds S x then θ none * ∏ j, θ (some (j,x j)) else 0 := by
  by_cases h : holds S x <;> simp [evaluate, mask, unaryWeight, h]

end
end Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
