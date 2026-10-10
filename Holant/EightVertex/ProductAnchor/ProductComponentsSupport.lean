import Holant.Tractable.Product
import Mathlib.Logic.Relation

/-! Connected components of the actual, possibly unbounded product-factor list.
Every equality or disequality relates its designated original ports. A connected
constraint graph has support in one complementary pair, even when unary factors
kill one of the two words. No tensor-prime normal-form hypothesis is used. -/
namespace Holant.EightVertex.ProductAnchor
open Holant Holant.Tractable
noncomputable section

variable {n : ℕ}

/-- Only actual binary factors make constraint-graph edges. -/
def FactorLinked (ps : List (ProductFactor n)) (i j : Fin n) : Prop :=
  ProductFactor.equality i j ∈ ps ∨ ProductFactor.disequality i j ∈ ps

def FactorConnected (ps : List (ProductFactor n)) (i j : Fin n) : Prop :=
  Relation.EqvGen (FactorLinked ps) i j

theorem factor_nonzero_of_formula_nonzero (a : AlgebraicComplex)
    (ps : List (ProductFactor n)) (x : Fin n → Bool)
    (hx : productFormula a ps x ≠ 0) (p : ProductFactor n) (hp : p ∈ ps) : p.eval x ≠ 0 := by
  intro hz
  apply hx
  have hm : 0 ∈ ps.map (fun q => q.eval x) := List.mem_map.mpr ⟨p,hp,hz⟩
  simp [productFormula,List.prod_eq_zero hm]

/-- Relative bit choices agree across each literal binary factor. -/
theorem linked_relative_bit (a : AlgebraicComplex) (ps : List (ProductFactor n))
    (s x : Fin n → Bool) (hs : productFormula a ps s ≠ 0)
    (hx : productFormula a ps x ≠ 0) {i j : Fin n} (h : FactorLinked ps i j) :
    (x i = s i ↔ x j = s j) := by
  rcases h with h | h
  · have hx' := factor_nonzero_of_formula_nonzero a ps x hx (.equality i j) h
    have hs' := factor_nonzero_of_formula_nonzero a ps s hs (.equality i j) h
    cases hxi : x i <;> cases hxj : x j <;> cases hsi : s i <;> cases hsj : s j <;>
      simp_all [ProductFactor.eval,Signature.equality]
  · have hx' := factor_nonzero_of_formula_nonzero a ps x hx (.disequality i j) h
    have hs' := factor_nonzero_of_formula_nonzero a ps s hs (.disequality i j) h
    cases hxi : x i <;> cases hxj : x j <;> cases hsi : s i <;> cases hsj : s j <;>
      simp_all [ProductFactor.eval,Signature.disequality]

/-- Connectivity propagates the relative bit through any number of factors. -/
theorem connected_relative_bit (a : AlgebraicComplex) (ps : List (ProductFactor n))
    (s x : Fin n → Bool) (hs : productFormula a ps s ≠ 0)
    (hx : productFormula a ps x ≠ 0) {i j : Fin n} (h : FactorConnected ps i j) :
    (x i = s i ↔ x j = s j) := by
  induction h with
  | rel i j h => exact linked_relative_bit a ps s x hs hx h
  | refl i => rfl
  | symm i j _ ih => exact ih.symm
  | trans i j k _ _ hij hjk => exact hij.trans hjk

/-- With all original coordinates connected to a chosen root, every supported
word is the chosen supported word or its bitwise complement. -/
theorem connected_support_pair (a : AlgebraicComplex) (ps : List (ProductFactor n))
    (root : Fin n) (hc : ∀ i, FactorConnected ps root i)
    (s x : Fin n → Bool) (hs : productFormula a ps s ≠ 0)
    (hx : productFormula a ps x ≠ 0) :
    x = s ∨ x = fun i => !(s i) := by
  by_cases hr : x root = s root
  · left
    funext i
    exact (connected_relative_bit a ps s x hs hx (hc i)).mp hr
  · right
    funext i
    have hi : x i ≠ s i := fun hi => hr ((connected_relative_bit a ps s x hs hx (hc i)).mpr hi)
    cases hxi : x i <;> cases hsi : s i <;> simp_all

/-- The component of a root is closed across every original binary factor. -/
theorem component_closed (ps : List (ProductFactor n)) (root : Fin n) {i j : Fin n}
    (h : FactorLinked ps i j) : FactorConnected ps root i ↔ FactorConnected ps root j := by
  constructor
  · intro hi
    exact Relation.EqvGen.trans _ _ _ hi (Relation.EqvGen.rel _ _ h)
  · intro hj
    exact Relation.EqvGen.trans _ _ _ hj (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h))

end
end Holant.EightVertex.ProductAnchor
