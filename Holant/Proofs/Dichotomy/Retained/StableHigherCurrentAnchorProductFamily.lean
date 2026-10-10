import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorProductBasis

/-! The Eq4 Product branch is literal, for the entire family at once. Monomial
coordinate changes preserve every actual Product factor, so no Product basis
search remains once the family contains the literal equality anchor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorProductFamily
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open StableHigherCurrentAnchorProductBasis
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The diagonal tensor multiplier is itself a product of unary factors. -/
theorem product_diagonalCoefficient {n : ℕ} (a b : AlgebraicComplex) :
    Product (fun x : Fin n → Bool => diagonalCoefficient a b x) := by
  have h (s : Finset (Fin n)) : Product (fun x : Fin n → Bool =>
      ∏ i ∈ s, if x i then b else a) := by
    induction s using Finset.induction_on with
    | empty => simpa using product_constant n 1
    | @insert i s hi ih =>
        simpa only [Finset.prod_insert hi] using
          (product_unary i (fun c => if c then b else a)).mul ih
  exact h Finset.univ

/-- Complementing every coordinate preserves the literal product class. -/
theorem product_complement {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Product f) : Product (fun x => f (complementWord x)) := by
  have hp (p : ProductFactor n) : Product (fun x => p.eval (complementWord x)) := by
    cases p with
    | unary i u hu => exact product_unary i (fun b => u (!b))
    | equality i j =>
        convert product_equality i j using 1
        funext x
        simp only [ProductFactor.eval,complementWord]
        cases x i <;> cases x j <;> rfl
    | disequality i j =>
        convert product_disequality i j using 1
        funext x
        simp only [ProductFactor.eval,complementWord]
        cases x i <;> cases x j <;> rfl
  rcases hf with rfl | ⟨a,ha,ps,rfl⟩
  · exact product_zero n
  · have hs : Product (fun x => (ps.map (fun p => p.eval (complementWord x))).prod) := by
      induction ps with
      | nil => simpa using product_constant n 1
      | cons p ps ih =>
          simpa only [List.map_cons,List.prod_cons] using (hp p).mul ih
    exact hs.scale a

/-- Any actual monomial tensor action preserves Product, in every arity. -/
theorem product_monomial_action (T : InvertibleKernel) (hT : Monomial T.matrix)
    {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Product f) : Product (T.action f) := by
  change Product (Signature.coordinateAction (fun _ => T.matrix) f)
  rcases hT with hT | hT
  · have he : T.matrix=diagonalKernel (T.matrix false false) (T.matrix true true) := by
      funext a b
      cases a <;> cases b <;> simp [diagonalKernel,hT.1,hT.2]
    rw [he,coordinateAction_diagonal]
    exact (product_diagonalCoefficient _ _).mul hf
  · have he : T.matrix=Kernel.mul
        (diagonalKernel (T.matrix false true) (T.matrix true false)) Signature.disequality := by
      funext a b
      cases a <;> cases b <;>
        simp [Kernel.mul_apply,diagonalKernel,Signature.disequality,hT.1,hT.2]
    rw [he,coordinateAction_antidiagonal]
    exact (product_diagonalCoefficient _ _).mul (product_complement hf)

/-- The inverse action gives the converse with the same actual basis. -/
theorem product_monomial_action_iff (T : InvertibleKernel) (hT : Monomial T.matrix)
    {n : ℕ} (f : Signature AlgebraicComplex n) : Product (T.action f) ↔ Product f := by
  constructor
  · intro h
    simpa only [InvertibleKernel.symm_action_action] using
      product_monomial_action T.symm (monomial_inverse T hT) h
  · exact product_monomial_action T hT

/-- A common Product basis for a family with Eq4 certifies every original
row in Product itself; all rows are pulled back with the one shared matrix. -/
theorem common_product_basis_literal {F : SignatureFamily AlgebraicComplex}
    (mem : (⟨4,eq4⟩ : AnySignature AlgebraicComplex) ∈ F)
    (B : InvertibleKernel) (hB : IsCommonBasis productClass F B) : F ⊆ productClass := by
  have hm := (common_product_basis_monomial mem B hB).1
  intro f hf
  have hp := product_monomial_action B hm (hB.2 f hf)
  change Product f.2
  simpa only [InvertibleKernel.action_symm_action] using hp

/-- Eq4 removes Product basis search for the entire family. Finiteness and
the original mandatory equality edge are retained in both directions. -/
theorem common_product_iff_literal {F : SignatureFamily AlgebraicComplex}
    (mem : (⟨4,eq4⟩ : AnySignature AlgebraicComplex) ∈ F) :
    CommonTransformable productClass F ↔ F.Finite ∧ F ⊆ productClass := by
  constructor
  · rintro ⟨finite,B,hB⟩
    exact ⟨finite,common_product_basis_literal mem B hB⟩
  · rintro ⟨finite,literal⟩
    apply commonTransformable_identity finite ?_ literal
    exact product_equality (0 : Fin 2) 1

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorProductFamily
end
