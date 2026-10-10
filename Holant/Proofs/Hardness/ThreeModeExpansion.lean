import Holant.Proofs.BinaryInterpolation.RawPolynomial
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Finite three-mode expansion of the actual network sum. The mode assignment
is a proof index, not an oracle signature or a promised evaluator. All unmarked
vertices, edges, loops, and parallel edges remain in their original positions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeExpansion
open Holant Holant.Complexity.BinaryInterpolation
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
variable (N : Network K n) (S : Finset (Fin N.shape.vertices))
variable (L : Fin 3 → (v : Fin N.shape.vertices) → Signature K (N.shape.arity v))
variable (eig : Fin 3 → K)

def sequenceNetwork (k : ℕ) : Network K n where
  shape := N.shape
  vertex v x := if v∈S then ∑i : Fin 3, (eig i)^(k+1)*L i v x else N.vertex v x
  edge := N.edge

def coefficient (σ : S → Fin 3) (x : Fin n → Bool) : K :=
  ∑z : (Fin N.shape.edges×Bool)→Bool,
    fixedWeight N S x z * ∏v : S,L (σ v) v.val (N.shape.assignment x z v.val)

def base (σ : S → Fin 3) : K := ∏v : S, eig (σ v)

/-- Complete exponential sum for the original incidence graph. -/
theorem sequence_expansion (k : ℕ) (x : Fin n → Bool) :
    (sequenceNetwork N S L eig k).denote x=
      ∑σ : S → Fin 3,coefficient N S L σ x*(base N S eig σ)^(k+1) := by
  classical
  unfold Network.denote sequenceNetwork
  simp only
  simp_rw [prod_cases S]
  have hp (z : (Fin N.shape.edges×Bool)→Bool) :
      (∏v∈S,∑i : Fin 3,eig i^(k+1)*L i v (N.shape.assignment x z v))=
        ∑σ : S → Fin 3,(base N S eig σ)^(k+1)*
          ∏v : S,L (σ v) v.val (N.shape.assignment x z v.val) := by
    rw [←Finset.prod_coe_sort S]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.prod_mul_distrib,Finset.prod_pow]
    rfl
  simp_rw [hp]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [coefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  simp only [fixedWeight]
  ring

/-- The all-zero proof index is exactly the graph with the desired mode. -/
theorem target_coefficient (x : Fin n → Bool) :
    coefficient N S L (fun _=>0) x=(rightNetwork N S (L 0)).denote x := by
  classical
  unfold coefficient Network.denote rightNetwork
  simp only
  apply Finset.sum_congr rfl
  intro z _
  rw [prod_cases S]
  change fixedWeight N S x z * (∏v : S,L 0 v.val (N.shape.assignment x z v.val))=_
  rw [Finset.prod_coe_sort S (fun v : Fin N.shape.vertices => L 0 v (N.shape.assignment x z v))]
  simp only [fixedWeight]
  ring

@[simp] theorem target_base : base N S eig (fun _=>0)=eig 0^S.card := by
  classical
  simp [base]

/-- A scalar filter acts on each true exponential mode separately. -/
theorem filter_expansion (d : ℕ) (p : ℕ → K) (x : Fin n → Bool) :
    (∑k∈Finset.range (d+1),p k*(sequenceNetwork N S L eig k).denote x)=
      ∑σ : S → Fin 3,coefficient N S L σ x*
        (∑k∈Finset.range (d+1),p k*(base N S eig σ)^(k+1)) := by
  classical
  simp_rw [sequence_expansion,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeExpansion
