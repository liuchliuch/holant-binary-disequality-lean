import Holant.Proofs.Recognition.TensorDecisionNormalization
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Holant.Tractable.Criteria

/-!
# Finite structural recognition of the source unary/binary tensor closure

`recognize` enumerates only bounded combinatorial port partitions and Boolean
input rows. For each nonzero pivot it builds the proposed factors by restricting
the original input table, divides by the pivot entry, and checks all original
rows. Neither a tensor decomposition nor its correctness is an input. In
particular the algorithm never invokes classical `decide` on tensor closure.

The executable field-parametric function uses field operations and decidable
entry equality. Its algebraic specialization is a structural table decision
procedure, not yet a machine on original algebraic descriptor bytes; this file
claims neither that latter implementation nor a polynomial recognition bound.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecision

open scoped BigOperators
open Holant.Tractable TensorDecisionNormalization

/-- A finite search space: at most `n` blocks, each of arity one or two,
and an exact ordered partition of the original `n` ports. -/
abbrev Shape (n : ℕ) :=
  Σ count : Fin (n + 1), Σ arity : Fin count.val → Fin 3,
    { _ports : (Σ i : Fin count.val, Fin (arity i).val) ≃ Fin n //
      ∀ i, (arity i).val = 1 ∨ (arity i).val = 2 }

namespace Shape
variable {n : ℕ}

abbrev count (S : Shape n) : ℕ := S.1.val
abbrev arity (S : Shape n) : Fin S.count → ℕ := fun i => (S.2.1 i).val
abbrev ports (S : Shape n) : (Σ i : Fin S.count, Fin (S.arity i)) ≃ Fin n := S.2.2.val

theorem allowed (S : Shape n) (i : Fin S.count) : S.arity i = 1 ∨ S.arity i = 2 :=
  S.2.2.property i

end Shape

variable {K : Type*} [Field K] {n : ℕ}

/-- Positive arity bounds the factor count by the number of original ports. -/
theorem count_le (D : TensorDecomposition K n) (hD : ∀ i, 0 < D.arity i) :
    D.count ≤ n := by
  let firstPort : Fin D.count → Fin n := fun i => D.ports ⟨i,⟨0,hD i⟩⟩
  have hinj : Function.Injective firstPort := by
    intro i j hij
    have h := D.ports.injective hij
    exact congrArg Sigma.fst h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective firstPort hinj

/-- Completeness supplies a finite shape from an existing mathematical
factorization; this proof-side map is not called by the recognition algorithm. -/
def shapeOfDecomposition (D : TensorDecomposition K n)
    (hD : ∀ i, D.arity i = 1 ∨ D.arity i = 2) : Shape n :=
  ⟨⟨D.count, Nat.lt_succ_of_le (count_le D (fun i => by rcases hD i with h | h <;> omega))⟩,
    (fun i => ⟨D.arity i, by rcases hD i with h | h <;> omega⟩), D.ports, hD⟩

/-- The candidate table for a searched shape and pivot; all its coefficients
are computed from literal entries of `f`. -/
def candidate (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool) :
    Signature K n := fun x => f pivot * ∏ i,
      normalizedSlice f S.count S.arity S.ports pivot i (fun j => x (S.ports ⟨i,j⟩))

/-- Finite row-by-row acceptance predicate, with a genuine input support pivot. -/
def Accepts (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool) : Prop :=
  f pivot ≠ 0 ∧ ∀ x, candidate f S pivot x = f x

/-- From an accepted finite check, construct the actual ordered tensor witness. -/
def decomposition (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool)
    (hp : f pivot ≠ 0) : TensorDecomposition K n where
  count := S.count
  arity := S.arity
  factor := normalizedSlice f S.count S.arity S.ports pivot
  ports := S.ports
  scale := Units.mk0 (f pivot) hp

@[simp] theorem decomposition_value (f : Signature K n) (S : Shape n)
    (pivot : Fin n → Bool) (hp : f pivot ≠ 0) :
    (decomposition f S pivot hp).value = candidate f S pivot := rfl

theorem accepts_sound (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool)
    (h : Accepts f S pivot) : Signature.TensorClosure (fun m _ => m = 1 ∨ m = 2) f :=
  ⟨decomposition f S pivot h.1, S.allowed, funext h.2⟩

theorem accepts_complete (D : TensorDecomposition K n)
    (hD : ∀ i, D.arity i = 1 ∨ D.arity i = 2)
    (pivot : Fin n → Bool) (hp : D.value pivot ≠ 0) :
    Accepts D.value (shapeOfDecomposition D hD) pivot :=
  ⟨hp, reconstruct D pivot hp⟩

/-- Mathematical specification with entirely finite witnesses and finite row tests. -/
def FiniteTest (f : Signature K n) : Prop :=
  (∀ x, f x = 0) ∨ ∃ S : Shape n, ∃ pivot : Fin n → Bool, Accepts f S pivot

/-- This finite test is equivalent to literal tensor closure with source zero convention. -/
theorem finiteTest_iff (f : Signature K n) :
    FiniteTest f ↔ f = 0 ∨ Signature.TensorClosure (fun m _ => m = 1 ∨ m = 2) f := by
  constructor
  · rintro (hz | ⟨S,p,h⟩)
    · exact Or.inl (funext hz)
    · exact Or.inr (accepts_sound f S p h)
  · rintro (rfl | ⟨D,hD,rfl⟩)
    · exact Or.inl (fun _ => rfl)
    · by_cases hz : D.value = 0
      · exact Or.inl (fun x => congrFun hz x)
      · have hp : ∃ p, D.value p ≠ 0 := by
          by_contra h
          push Not at h
          exact hz (funext h)
        obtain ⟨p,hp⟩ := hp
        exact Or.inr ⟨shapeOfDecomposition D hD,p,accepts_complete D hD p hp⟩

section Executable
variable [DecidableEq K]

instance (f : Signature K n) (S : Shape n) (pivot : Fin n → Bool) :
    Decidable (Accepts f S pivot) :=
  inferInstanceAs (Decidable (f pivot ≠ 0 ∧ ∀ x, candidate f S pivot x = f x))

instance (f : Signature K n) : Decidable (FiniteTest f) :=
  inferInstanceAs (Decidable
    ((∀ x, f x = 0) ∨ ∃ S : Shape n, ∃ pivot : Fin n → Bool, Accepts f S pivot))

/-- Exhaustive finite structural recognition, relative only to exact field operations
and entry equality. This is `decide` on the displayed finite table test, never
on the infinitary/existential source tensor predicate. -/
def recognize (f : Signature K n) : Bool := decide (FiniteTest f)

theorem recognize_eq_true_iff (f : Signature K n) : recognize f = true ↔
    f = 0 ∨ Signature.TensorClosure (fun m _ => m = 1 ∨ m = 2) f := by
  rw [recognize, decide_eq_true_eq]
  exact finiteTest_iff f

end Executable

/-- The exact original algebraic-signature source predicate, without a supplied
factorization. Equality of algebraic entries still requires its separate effective
representation when compiling this structural test to a byte machine. -/
theorem source_iff_finiteTest (f : Signature AlgebraicComplex n) :
    SourceTensorClosure (fun m _ => m = 1 ∨ m = 2) f ↔ FiniteTest f :=
  (finiteTest_iff f).symm

/-- Semantic algebraic specialization: only coefficient equality is classical.
The searched predicate is still the explicit finite structural test above. -/
noncomputable def recognizeOriginal (f : Signature AlgebraicComplex n) : Bool := by
  classical
  exact recognize f

theorem recognizeOriginal_eq_true_iff (f : Signature AlgebraicComplex n) :
    recognizeOriginal f = true ↔ SourceTensorClosure (fun m _ => m = 1 ∨ m = 2) f := by
  classical
  exact recognize_eq_true_iff f

noncomputable def recognizeFamily {s : ℕ} (arity : Fin s → ℕ)
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i)) : Bool :=
  decide (∀ i, recognizeOriginal (G i) = true)

theorem recognizeFamily_eq_true_iff {s : ℕ} (arity : Fin s → ℕ)
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i)) :
    recognizeFamily arity G = true ↔
      ∀ i, SourceTensorClosure (fun m _ => m = 1 ∨ m = 2) (G i) := by
  simp only [recognizeFamily, decide_eq_true_eq, recognizeOriginal_eq_true_iff]

end Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecision
