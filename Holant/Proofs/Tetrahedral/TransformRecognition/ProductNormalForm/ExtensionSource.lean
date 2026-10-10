import Holant.Proofs.Tetrahedral.TransformRecognition.ProductNormalForm.Polynomials


namespace Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.ExtensionSource
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Tractable
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Source factors retain the nonzero-as-a-function unary convention. Values
at individual bits may vanish, and different unary factors may annihilate. -/
inductive Factor (E : Type*) [Zero E] (n : ℕ) where
  | unary (port : Fin n) (values : Bool → E) (nonzero : values ≠ 0)
  | equality (left right : Fin n)
  | disequality (left right : Fin n)

variable {E : Type*} [Field E] {n : ℕ}

def Factor.eval : Factor E n → Signature E n
  | .unary j u _ => fun x => u (x j)
  | .equality j k => fun x => Signature.equality (x j) (x k)
  | .disequality j k => fun x => Signature.disequality (x j) (x k)

def formula (c : E) (fs : List (Factor E n)) : Signature E n :=
  fun x => c * (fs.map (fun h => h.eval x)).prod

/-- Actual source Product with free coefficients in E, independently defined
using arbitrary finite lists. No algebraicity, template, or length premise. -/
def ProductOver (f : Signature E n) : Prop :=
  f = 0 ∨ ∃ c : E, c ≠ 0 ∧ ∃ fs : List (Factor E n), f = formula c fs

theorem zero_product : ProductOver (0 : Signature E n) := Or.inl rfl

theorem formula_product (c : E) (fs : List (Factor E n)) : ProductOver (formula c fs) := by
  by_cases hc : c = 0
  · left
    subst c
    funext x
    simp [formula]
  · exact Or.inr ⟨c,hc,fs,rfl⟩

theorem constant_product (c : E) : ProductOver (fun _ : Fin n → Bool => c) := by
  have he : formula c ([] : List (Factor E n)) = (fun _ : Fin n → Bool => c) := by
    funext x
    simp [formula]
  rw [←he]
  exact formula_product c []

theorem factor_product (h : Factor E n) : ProductOver h.eval := by
  have he : formula 1 [h] = h.eval := by
    funext x
    simp [formula]
  rw [←he]
  exact formula_product 1 [h]

theorem unary_product (j : Fin n) (u : Bool → E) : ProductOver (fun x => u (x j)) := by
  by_cases hu : u = 0
  · subst u
    exact zero_product
  · exact factor_product (.unary j u hu)

theorem ProductOver.scale {f : Signature E n} (hf : ProductOver f) (c : E) :
    ProductOver (fun x => c * f x) := by
  rcases hf with rfl | ⟨d,hd,fs,rfl⟩
  · left
    funext x
    simp
  · convert formula_product (c*d) fs using 1
    funext x
    simp [formula, mul_assoc]

theorem ProductOver.mul {f g : Signature E n} (hf : ProductOver f) (hg : ProductOver g) :
    ProductOver (fun x => f x * g x) := by
  rcases hf with rfl | ⟨c,hc,fs,rfl⟩
  · left
    funext x
    simp
  rcases hg with rfl | ⟨d,hd,gs,rfl⟩
  · left
    funext x
    simp
  convert formula_product (c*d) (fs ++ gs) using 1
  funext x
  simp [formula, List.prod_append]
  ring

/-- Constraint insertion has set/idempotent semantics. Equality loops vanish
from the code; contradictory edges need no special nonzero assumption. -/
def code : List (Factor E n) → Skeleton n
  | [] => ∅
  | .unary _ _ _ :: fs => code fs
  | .equality j k :: fs => if j = k then code fs else insert (equalEdge j k) (code fs)
  | .disequality j k :: fs => insert (unequalEdge j k) (code fs)

def unaryPart : Factor E n → Fin n → Bool → E
  | .unary k u _, j, b => if j = k then u b else 1
  | .equality _ _, _, _ => 1
  | .disequality _ _, _, _ => 1

def merged : List (Factor E n) → Fin n → Bool → E
  | [], _, _ => 1
  | h :: fs, j, b => unaryPart h j b * merged fs j b

def parameters (c : E) (fs : List (Factor E n)) : Parameter n → E
  | none => c
  | some (j,b) => merged fs j b

theorem merged_entry (fs : List (Factor E n)) (j : Fin n) (b : Bool) :
    merged fs j b = (fs.map (fun h => unaryPart h j b)).prod := by
  induction fs with
  | nil => rfl
  | cons h fs ih => simp only [merged, List.map_cons, List.prod_cons, ih]

theorem weight_unary (j : Fin n) (u : Bool → E) (hu : u ≠ 0) (x : Fin n → Bool) :
    unaryWeight (unaryPart (.unary j u hu)) x = u (x j) := by
  unfold unaryWeight
  calc
    (∏ k, unaryPart (.unary j u hu) k (x k)) = unaryPart (.unary j u hu) j (x j) := by
      apply Finset.prod_eq_single j
      · intro k hk hkj
        simp [unaryPart, hkj]
      · simp
    _ = u (x j) := by simp [unaryPart]

theorem weight_cons (h : Factor E n) (fs : List (Factor E n)) (x : Fin n → Bool) :
    unaryWeight (merged (h :: fs)) x = unaryWeight (unaryPart h) x * unaryWeight (merged fs) x := by
  exact Finset.prod_mul_distrib

theorem cons_exact (h : Factor E n) (fs : List (Factor E n)) (x : Fin n → Bool) :
    mask (code (h :: fs)) x * unaryWeight (merged (h :: fs)) x =
      h.eval x * (mask (code fs) x * unaryWeight (merged fs) x) := by
  rw [weight_cons]
  cases h with
  | unary j u hu =>
    rw [weight_unary]
    change mask (code fs) x * (u (x j) * unaryWeight (merged fs) x) =
      u (x j) * (mask (code fs) x * unaryWeight (merged fs) x)
    ring
  | equality j k =>
    by_cases hjk : j = k
    · subst k
      simp [code, unaryWeight, unaryPart, Factor.eval, Signature.equality]
    · simp [code, hjk, mask_insert, edgeMask_equal, unaryWeight, unaryPart, Factor.eval, mul_assoc]
  | disequality j k =>
    simp [code, mask_insert, edgeMask_unequal, unaryWeight, unaryPart, Factor.eval, mul_assoc]

theorem factors_exact (fs : List (Factor E n)) (x : Fin n → Bool) :
    (fs.map (fun h => h.eval x)).prod = mask (code fs) x * unaryWeight (merged fs) x := by
  induction fs with
  | nil => simp [code, merged, mask, unaryWeight]
  | cons h fs ih =>
    rw [List.map_cons, List.prod_cons, ih]
    exact (cons_exact h fs x).symm

/-- Generalized normalization uses the existing finite Skeleton/Parameter
types and existing evaluate; every coefficient remains in the supplied E. -/
theorem normalize_formula (c : E) (fs : List (Factor E n)) :
    formula c fs = evaluate (code fs) (parameters c fs) := by
  funext x
  simp only [formula, factors_exact, evaluate, parameters, mul_assoc]

theorem normalized_bounds (fs : List (Factor E n)) :
    code fs ∈ allSkeletons n ∧ (code fs).card ≤ 2*n*n ∧
      Fintype.card (Parameter n) = 1+2*n := by
  refine ⟨Finset.mem_univ _,?_,parameter_count n⟩
  simpa only [edge_count] using Finset.card_le_univ (code fs)

theorem edge_product (e : Edge n) : ProductOver (fun x => edgeMask (K := E) e x) := by
  obtain ⟨⟨j,k⟩,b⟩ := e
  cases b
  · change ProductOver (fun x => edgeMask (K := E) (unequalEdge j k) x)
    simpa only [edgeMask_unequal, Factor.eval] using factor_product (Factor.disequality (E := E) j k)
  · change ProductOver (fun x => edgeMask (K := E) (equalEdge j k) x)
    simpa only [edgeMask_equal, Factor.eval] using factor_product (Factor.equality (E := E) j k)

theorem mask_product (S : Skeleton n) : ProductOver (fun x => mask (K := E) S x) := by
  induction S using Finset.induction_on with
  | empty => simpa [mask] using constant_product (n := n) (1 : E)
  | insert e S he ih =>
    have hm : (fun x => mask (K := E) (insert e S) x) =
        (fun x => edgeMask e x * mask S x) := funext (mask_insert S e)
    rw [hm]
    exact (edge_product e).mul ih

theorem product_finset {ι : Type*} (s : Finset ι) (F : ι → Signature E n)
    (h : ∀ i ∈ s, ProductOver (F i)) : ProductOver (fun x => ∏ i ∈ s, F i x) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simpa using constant_product (n := n) (1 : E)
  | insert a s ha ih =>
    intro h
    have ht : ProductOver (fun x => ∏ i ∈ s, F i x) :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.prod_insert ha] using (h a (Finset.mem_insert_self a s)).mul ht

theorem unaryWeight_product (u : Fin n → Bool → E) : ProductOver (unaryWeight u) :=
  product_finset Finset.univ (fun j x => u j (x j)) (fun j _ => unary_product j (u j))

theorem evaluate_product (S : Skeleton n) (θ : Parameter n → E) : ProductOver (evaluate S θ) := by
  have h := ((mask_product S).mul (unaryWeight_product (fun j b => θ (some (j,b))))).scale (θ none)
  convert h using 1
  funext x
  simp only [evaluate, mul_assoc]

/-- Source-definition bridge, not a definition by the desired finite result. -/
theorem productOver_iff (f : Signature E n) :
    ProductOver f ↔ ∃ S : Skeleton n, ∃ θ : Parameter n → E, f = evaluate S θ := by
  constructor
  · rintro (rfl | ⟨c,hc,fs,hf⟩)
    · refine ⟨∅,fun _ => 0,?_⟩
      funext x
      simp [evaluate]
    · exact ⟨code fs,parameters c fs,hf.trans (normalize_formula c fs)⟩
  · rintro ⟨S,θ,rfl⟩
    exact evaluate_product S θ

theorem finite_enumeration (f : Signature E n) :
    ProductOver f ↔ ∃ S ∈ allSkeletons n, ∃ θ : Parameter n → E, f = evaluate S θ := by
  simpa only [allSkeletons, Finset.mem_univ, true_and] using productOver_iff f

/-- Reuses the delivered generic polynomial evaluation theorem. In particular
E may be C; free coefficients are not assumed algebraic in this theorem. -/
theorem polynomial_coverage {R : Type*} [CommSemiring R] (φ : R →+* E)
    (f : Signature E n) :
    ProductOver f ↔ ∃ S ∈ allSkeletons n, ∃ θ : Parameter n → E,
      ∀ x, f x = MvPolynomial.eval₂ φ θ (entryPolynomial R S x) := by
  rw [finite_enumeration]
  constructor
  · rintro ⟨S,hS,θ,rfl⟩
    exact ⟨S,hS,θ,fun x => (eval₂_entry φ S θ x).symm⟩
  · rintro ⟨S,hS,θ,hθ⟩
    exact ⟨S,hS,θ,funext (fun x => (hθ x).trans (eval₂_entry φ S θ x))⟩

/-- Every nullary table is a scalar, including zero and the empty product. -/
theorem nullary_product (f : Signature E 0) : ProductOver f := by
  let x₀ : Fin 0 → Bool := Fin.elim0
  have he : f = fun _ => f x₀ := by
    funext x
    have hx : x = x₀ := by ext j; exact Fin.elim0 j
    rw [hx]
  rw [he]
  exact constant_product _

theorem merged_zero_formula (c : E) (fs : List (Factor E n)) (j : Fin n)
    (h : ∀ b, merged fs j b = 0) : formula c fs = 0 := by
  rw [normalize_formula]
  exact zero_unary _ _ j h

theorem equality_loop_formula (c : E) (fs : List (Factor E n)) (j : Fin n) :
    formula c (.equality j j :: fs) = formula c fs := by
  funext x
  simp [formula, Factor.eval, Signature.equality]

theorem disequality_loop_formula (c : E) (fs : List (Factor E n)) (j : Fin n) :
    formula c (.disequality j j :: fs) = 0 := by
  funext x
  simp [formula, Factor.eval, Signature.disequality]

theorem opposite_factors_formula (c : E) (fs : List (Factor E n)) (j k : Fin n) :
    formula c (.equality j k :: .disequality j k :: fs) = 0 := by
  funext x
  by_cases h : x j = x k <;>
    simp [formula, Factor.eval, Signature.equality, Signature.disequality, h]

/-- The complex source class really allows arbitrary complex unary/scalar
values. This is the interface for the source hypothesis of 2.13. -/
theorem complex_product_iff (f : Signature ℂ n) :
    ProductOver f ↔ ∃ S ∈ allSkeletons n, ∃ θ : Parameter n → ℂ, f = evaluate S θ :=
  finite_enumeration f

/-- Complex membership compiles into the existing algebraic-coefficient
template polynomials; the parameter tuple itself is still unrestricted C. -/
theorem complex_polynomial_coverage (f : Signature ℂ n) :
    ProductOver f ↔ ∃ S ∈ allSkeletons n, ∃ θ : Parameter n → ℂ,
      ∀ x, f x = MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).subtype θ
        (entryPolynomial AlgebraicComplex S x) :=
  polynomial_coverage (algebraicClosure ℚ ℂ).subtype f

/-- Specialization preserves the original unary value and its exact nonzero
proof; equality/disequality constructors retain both original port indices. -/
def Factor.toOriginal : Factor AlgebraicComplex n → ProductFactor n
  | .unary j u hu => .unary j u hu
  | .equality j k => .equality j k
  | .disequality j k => .disequality j k

def Factor.ofOriginal : ProductFactor n → Factor AlgebraicComplex n
  | .unary j u hu => .unary j u hu
  | .equality j k => .equality j k
  | .disequality j k => .disequality j k

theorem Factor.original_roundtrip (h : ProductFactor n) :
    (Factor.ofOriginal h).toOriginal = h := by cases h <;> rfl

theorem Factor.extension_roundtrip (h : Factor AlgebraicComplex n) :
    Factor.ofOriginal h.toOriginal = h := by cases h <;> rfl

theorem Factor.eval_toOriginal (h : Factor AlgebraicComplex n) : h.toOriginal.eval = h.eval := by
  cases h <;> rfl

theorem Factor.eval_ofOriginal (h : ProductFactor n) : (Factor.ofOriginal h).eval = h.eval := by
  cases h <;> rfl

theorem formula_toOriginal (c : AlgebraicComplex) (fs : List (Factor AlgebraicComplex n)) :
    productFormula c (fs.map Factor.toOriginal) = formula c fs := by
  funext x
  simp [productFormula, formula, List.map_map, Function.comp_def, Factor.eval_toOriginal]

theorem formula_ofOriginal (c : AlgebraicComplex) (fs : List (ProductFactor n)) :
    formula c (fs.map Factor.ofOriginal) = productFormula c fs := by
  funext x
  simp [productFormula, formula, List.map_map, Function.comp_def, Factor.eval_ofOriginal]

/-- Direct list-level identification with the existing Product class; this
does not pass through an assumed semantic equivalence or template oracle. -/
theorem productOver_algebraic_iff (f : Signature AlgebraicComplex n) :
    ProductOver f ↔ Holant.Tractable.Product f := by
  constructor
  · rintro (hz | ⟨c,hc,fs,hf⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨c,hc,fs.map Factor.toOriginal,hf.trans (formula_toOriginal c fs).symm⟩
  · rintro (hz | ⟨c,hc,fs,hf⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨c,hc,fs.map Factor.ofOriginal,hf.trans (formula_ofOriginal c fs).symm⟩

end
end Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.ExtensionSource
