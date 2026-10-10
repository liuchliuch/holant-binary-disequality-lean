import Holant.Proofs.Tetrahedral.TransformRecognition.ProductNormalForm.Normalization


namespace Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open Holant Holant.Tractable
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem edge_product (e : Edge n) :
    Product (fun x => edgeMask (K := AlgebraicComplex) e x) := by
  obtain ⟨⟨j,k⟩,b⟩ := e
  cases b
  · change Product (fun x => edgeMask (K := AlgebraicComplex) (unequalEdge j k) x)
    simpa only [edgeMask_unequal] using product_disequality j k
  · change Product (fun x => edgeMask (K := AlgebraicComplex) (equalEdge j k) x)
    simpa only [edgeMask_equal] using product_equality j k

theorem mask_product (S : Skeleton n) :
    Product (fun x => mask (K := AlgebraicComplex) S x) := by
  induction S using Finset.induction_on with
  | empty => simpa [mask] using product_constant n 1
  | insert e S he ih =>
    have hm : (fun x => mask (K := AlgebraicComplex) (insert e S) x) =
        (fun x => edgeMask e x * mask S x) := funext (mask_insert S e)
    rw [hm]
    exact (edge_product e).mul ih

theorem product_finset {ι : Type*} (s : Finset ι) (F : ι → Signature AlgebraicComplex n)
    (h : ∀ i ∈ s, Product (F i)) : Product (fun x => ∏ i ∈ s, F i x) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simpa using product_constant n 1
  | insert a s ha ih =>
    intro h
    have htail : Product (fun x => ∏ i ∈ s, F i x) :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.prod_insert ha] using (h a (Finset.mem_insert_self a s)).mul htail

theorem unaryWeight_product (u : Fin n → Bool → AlgebraicComplex) :
    Product (unaryWeight u) := by
  exact product_finset Finset.univ (fun j x => u j (x j))
    (fun j _ => product_unary j (u j))

/-- Every template, including every zero-parameter branch, is genuinely Product. -/
theorem evaluate_product (S : Skeleton n) (θ : Parameter n → AlgebraicComplex) :
    Product (evaluate S θ) := by
  have h := ((mask_product S).mul
    (unaryWeight_product (fun j b => θ (some (j,b))))).scale (θ none)
  convert h using 1
  funext x
  simp only [evaluate, mul_assoc]

/-- Exact finite-skeleton coverage. No normal-form or finiteness oracle is an input. -/
theorem product_iff (f : Signature AlgebraicComplex n) :
    Product f ↔ ∃ S : Skeleton n, ∃ θ : Parameter n → AlgebraicComplex, f = evaluate S θ := by
  constructor
  · rintro (rfl | ⟨c,hc,fs,hf⟩)
    · refine ⟨∅,fun _ => 0,?_⟩
      funext x
      simp [evaluate]
    · exact ⟨skeleton fs,parameters c fs,hf.trans (normalize_formula c fs)⟩
  · rintro ⟨S,θ,rfl⟩
    exact evaluate_product S θ

/-- Explicit finite enumeration, with only 1+2n free algebraic coefficients. -/
theorem finite_enumeration (f : Signature AlgebraicComplex n) :
    Product f ↔ ∃ S ∈ allSkeletons n, ∃ θ : Parameter n → AlgebraicComplex,
      f = evaluate S θ := by
  simpa only [allSkeletons, Finset.mem_univ, true_and] using product_iff f

theorem coefficientwise_recognition (f : Signature AlgebraicComplex n) :
    Product f ↔ ∃ S ∈ allSkeletons n, ∃ θ : Parameter n → AlgebraicComplex,
      ∀ x : Fin n → Bool,
        f x = if holds S x then θ none * ∏ j, θ (some (j,x j)) else 0 := by
  rw [finite_enumeration]
  constructor
  · rintro ⟨S,hS,θ,rfl⟩
    exact ⟨S,hS,θ,entry_formula S θ⟩
  · rintro ⟨S,hS,θ,hθ⟩
    refine ⟨S,hS,θ,?_⟩
    funext x
    exact (hθ x).trans (entry_formula S θ x).symm

/-- The bounds apply to every input list; no factor multiplicity is an
additional parameter or part of the finite combinatorial search. -/
theorem normalized_template_bounds (fs : List (ProductFactor n)) :
    skeleton fs ∈ allSkeletons n ∧ (skeleton fs).card ≤ 2*n*n ∧
      Fintype.card (Parameter n) = 1+2*n ∧ (allSkeletons n).card = 2^(2*n*n) :=
  ⟨Finset.mem_univ _,normalized_edges_bounded fs,parameter_count n,allSkeletons_count n⟩

end
end Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
