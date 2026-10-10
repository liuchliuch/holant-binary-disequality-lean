import Holant.Proofs.Tractability.ProductEliminationBounds


namespace Holant.LocalDrafts.Tractability.ProductElimination

open Holant.Tractable
open scoped BigOperators

def fromSourceFactor {n : ℕ} : ProductFactor n → Factor AlgebraicComplex n
  | .unary j u _ => .unary j u
  | .equality a b => .link a b false
  | .disequality a b => .link a b true

theorem fromSourceFactor_eval {n : ℕ} (f : ProductFactor n) (x : Fin n → Bool) :
    (fromSourceFactor f).eval x = f.eval x := by
  cases f with
  | unary j u h => rfl
  | equality a b =>
    simp only [fromSourceFactor, Factor.eval, ProductFactor.eval]
    cases x a <;> cases x b <;> rfl
  | disequality a b =>
    simp only [fromSourceFactor, Factor.eval, ProductFactor.eval]
    cases x a <;> cases x b <;> rfl

def fromSource {n : ℕ} (scale : AlgebraicComplex) (fs : List (ProductFactor n)) :
    List (Factor AlgebraicComplex n) := .scalar scale :: fs.map fromSourceFactor

theorem fromSource_weight {n : ℕ} (scale : AlgebraicComplex)
    (fs : List (ProductFactor n)) (x : Fin n → Bool) :
    weight (fromSource scale fs) x = productFormula scale fs x := by
  simp only [fromSource, weight, List.map_cons, List.prod_cons, List.map_map,
    Function.comp_def, fromSourceFactor_eval, productFormula]
  rfl

/-- Local tensor data, not an algorithm or a global Holant-value premise. -/
structure Presentation {n : ℕ} (f : Signature AlgebraicComplex n) where
  factors : List (Factor AlgebraicComplex n)
  localFormula : ∀ x, weight factors x = f x

theorem presentation_exists {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Product f) : Nonempty (Presentation f) := by
  rcases hf with rfl | ⟨c, _, fs, rfl⟩
  · exact ⟨⟨[.scalar 0], by intro x; simp [Factor.eval]⟩⟩
  · exact ⟨⟨fromSource c fs, fromSource_weight c fs⟩⟩

noncomputable def ofProduct {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Product f) : Presentation f := Classical.choice (presentation_exists hf)

theorem evaluate_source_formula {n : ℕ} (scale : AlgebraicComplex)
    (fs : List (ProductFactor n)) :
    evaluate (fromSource scale fs) = ∑ x, productFormula scale fs x := by
  rw [evaluate_eq_partition]
  simp only [partition, fromSource_weight]

theorem evaluate_presentation {n : ℕ} {f : Signature AlgebraicComplex n}
    (P : Presentation f) : evaluate P.factors = ∑ x, f x := by
  rw [evaluate_eq_partition]
  simp only [partition, P.localFormula]

end Holant.LocalDrafts.Tractability.ProductElimination
