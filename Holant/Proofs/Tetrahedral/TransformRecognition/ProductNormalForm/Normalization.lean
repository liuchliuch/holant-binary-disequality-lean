import Holant.Proofs.Tetrahedral.TransformRecognition.ProductNormalForm.Templates


namespace Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open Holant Holant.Tractable
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def skeleton : List (ProductFactor n) → Skeleton n
  | [] => ∅
  | .unary _ _ _ :: fs => skeleton fs
  | .equality j k :: fs => if j = k then skeleton fs else insert (equalEdge j k) (skeleton fs)
  | .disequality j k :: fs => insert (unequalEdge j k) (skeleton fs)

def unaryPart : ProductFactor n → Fin n → Bool → AlgebraicComplex
  | .unary k u _, j, b => if j = k then u b else 1
  | .equality _ _, _, _ => 1
  | .disequality _ _, _, _ => 1

def merged : List (ProductFactor n) → Fin n → Bool → AlgebraicComplex
  | [], _, _ => 1
  | h :: fs, j, b => unaryPart h j b * merged fs j b

def parameters (c : AlgebraicComplex) (fs : List (ProductFactor n)) :
    Parameter n → AlgebraicComplex
  | none => c
  | some (j,b) => merged fs j b

theorem merged_entry (fs : List (ProductFactor n)) (j : Fin n) (b : Bool) :
    merged fs j b = (fs.map (fun h => unaryPart h j b)).prod := by
  induction fs with
  | nil => rfl
  | cons h fs ih => simp only [merged, List.map_cons, List.prod_cons, ih]

theorem merged_append (fs gs : List (ProductFactor n)) (j : Fin n) (b : Bool) :
    merged (fs ++ gs) j b = merged fs j b * merged gs j b := by
  simp only [merged_entry, List.map_append, List.prod_append]

theorem skeleton_append (fs gs : List (ProductFactor n)) :
    skeleton (fs ++ gs) = skeleton fs ∪ skeleton gs := by
  induction fs with
  | nil => simp [skeleton]
  | cons h fs ih =>
    cases h with
    | unary j u hu => simpa only [List.cons_append, skeleton] using ih
    | equality j k =>
      by_cases h : j = k <;> simp [skeleton, h, ih]
    | disequality j k => simp [skeleton, ih]

theorem weight_unary (j : Fin n) (u : Bool → AlgebraicComplex) (hu : u ≠ 0)
    (x : Fin n → Bool) : unaryWeight (unaryPart (.unary j u hu)) x = u (x j) := by
  unfold unaryWeight
  calc
    (∏ k, unaryPart (.unary j u hu) k (x k)) = unaryPart (.unary j u hu) j (x j) := by
      apply Finset.prod_eq_single j
      · intro k hk hkj
        simp [unaryPart, hkj]
      · simp
    _ = u (x j) := by simp [unaryPart]

theorem weight_merged_cons (h : ProductFactor n) (fs : List (ProductFactor n))
    (x : Fin n → Bool) :
    unaryWeight (merged (h :: fs)) x = unaryWeight (unaryPart h) x * unaryWeight (merged fs) x := by
  exact Finset.prod_mul_distrib

/-- The inductive identity uses idempotent constraint insertion, not parity. -/
theorem cons_exact (h : ProductFactor n) (fs : List (ProductFactor n)) (x : Fin n → Bool) :
    mask (skeleton (h :: fs)) x * unaryWeight (merged (h :: fs)) x =
      h.eval x * (mask (skeleton fs) x * unaryWeight (merged fs) x) := by
  rw [weight_merged_cons]
  cases h with
  | unary j u hu =>
    rw [weight_unary]
    change mask (skeleton fs) x * (u (x j) * unaryWeight (merged fs) x) =
      u (x j) * (mask (skeleton fs) x * unaryWeight (merged fs) x)
    ring
  | equality j k =>
    by_cases hjk : j = k
    · subst k
      simp [skeleton, unaryWeight, unaryPart, ProductFactor.eval, Signature.equality]
    · simp [skeleton, hjk, mask_insert, edgeMask_equal,
        unaryWeight, unaryPart, ProductFactor.eval, mul_assoc]
  | disequality j k =>
    simp [skeleton, mask_insert, edgeMask_unequal,
      unaryWeight, unaryPart, ProductFactor.eval, mul_assoc]

theorem factors_exact (fs : List (ProductFactor n)) (x : Fin n → Bool) :
    (fs.map (fun h => h.eval x)).prod =
      mask (skeleton fs) x * unaryWeight (merged fs) x := by
  induction fs with
  | nil => simp [skeleton, merged, mask, unaryWeight]
  | cons h fs ih =>
    rw [List.map_cons, List.prod_cons, ih]
    exact (cons_exact h fs x).symm

/-- Every original formula has a fixed-size template, including zero scale,
inconsistent edges, vanishing merged unaries, and the empty/nullary formula. -/
theorem normalize_formula (c : AlgebraicComplex) (fs : List (ProductFactor n)) :
    productFormula c fs = evaluate (skeleton fs) (parameters c fs) := by
  funext x
  simp only [productFormula, factors_exact, evaluate, parameters, mul_assoc]

theorem normalized_edges_bounded (fs : List (ProductFactor n)) :
    (skeleton fs).card ≤ 2*n*n := by
  calc
    (skeleton fs).card ≤ Fintype.card (Edge n) := Finset.card_le_univ _
    _ = 2*n*n := edge_count n

theorem equality_loop_deleted (j : Fin n) (fs : List (ProductFactor n)) :
    skeleton (.equality j j :: fs) = skeleton fs := by simp [skeleton]

theorem repeated_equality (j k : Fin n) (fs : List (ProductFactor n)) :
    skeleton (.equality j k :: .equality j k :: fs) = skeleton (.equality j k :: fs) := by
  by_cases h : j = k <;> simp [skeleton, h]

theorem repeated_disequality (j k : Fin n) (fs : List (ProductFactor n)) :
    skeleton (.disequality j k :: .disequality j k :: fs) = skeleton (.disequality j k :: fs) := by
  simp [skeleton]

/-- Even two copies of a disequality still forbid equal bits. -/
theorem repeated_disequality_not_parity (j k : Fin n) (c : AlgebraicComplex)
    (fs : List (ProductFactor n)) (x : Fin n → Bool) (hx : x j = x k) :
    productFormula c (.disequality j k :: .disequality j k :: fs) x = 0 := by
  simp [productFormula, ProductFactor.eval, Signature.disequality, hx]

theorem opposing_factors_zero (j k : Fin n) (c : AlgebraicComplex)
    (fs : List (ProductFactor n)) :
    productFormula c (.equality j k :: .disequality j k :: fs) = 0 := by
  funext x
  by_cases h : x j = x k <;>
    simp [productFormula, ProductFactor.eval, Signature.equality, Signature.disequality, h]

/-- A merged zero unary is allowed even though source unary factors are
individually nonzero as functions. No division or nonzero-product premise. -/
theorem merged_zero_formula (c : AlgebraicComplex) (fs : List (ProductFactor n))
    (j : Fin n) (h : ∀ b, merged fs j b = 0) : productFormula c fs = 0 := by
  rw [normalize_formula]
  exact zero_unary _ _ j h

end
end Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
