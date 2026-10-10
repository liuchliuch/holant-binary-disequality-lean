import Holant.Tractable.AffineOperations
import Holant.Tractable.Product

/-! Disjoint tensors retain both actual tractable-class failures. The coordinate
restrictions in this file are semantic class reflection, not oracle pins. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
set_option backward.isDefEq.respectTransparency false

/-- Each old coordinate is either a fixed bit or an actual new coordinate. -/
def substitute {m n : ℕ} (p : Fin n → Bool ⊕ Fin m) (x : Fin m → Bool) : Fin n → Bool :=
  fun j => Sum.elim id x (p j)

theorem product_substitute {m n : ℕ} (p : Fin n → Bool ⊕ Fin m)
    {f : Signature AlgebraicComplex n} (hf : Product f) :
    Product (fun x => f (substitute p x)) := by
  have factor (r : ProductFactor n) : Product (fun x => r.eval (substitute p x)) := by
    cases r with
    | unary i u hu =>
      cases hi : p i with
      | inl b => simpa [substitute, ProductFactor.eval, hi] using product_constant m (u b)
      | inr j => simpa [substitute, ProductFactor.eval, hi] using product_unary j u
    | equality i j =>
      cases hi : p i with
      | inl b =>
        cases hj : p j with
        | inl c => simpa [substitute, ProductFactor.eval, hi, hj] using
            product_constant m (Signature.equality (K:=AlgebraicComplex) b c)
        | inr k => simpa [substitute, ProductFactor.eval, hi, hj] using
            product_unary k (fun c => Signature.equality (K:=AlgebraicComplex) b c)
      | inr k =>
        cases hj : p j with
        | inl c => simpa [substitute, ProductFactor.eval, hi, hj] using
            product_unary k (fun b => Signature.equality (K:=AlgebraicComplex) b c)
        | inr l => simpa [substitute, ProductFactor.eval, hi, hj] using product_equality k l
    | disequality i j =>
      cases hi : p i with
      | inl b =>
        cases hj : p j with
        | inl c => simpa [substitute, ProductFactor.eval, hi, hj] using
            product_constant m (Signature.disequality (K:=AlgebraicComplex) b c)
        | inr k => simpa [substitute, ProductFactor.eval, hi, hj] using
            product_unary k (fun c => Signature.disequality (K:=AlgebraicComplex) b c)
      | inr k =>
        cases hj : p j with
        | inl c => simpa [substitute, ProductFactor.eval, hi, hj] using
            product_unary k (fun b => Signature.disequality (K:=AlgebraicComplex) b c)
        | inr l => simpa [substitute, ProductFactor.eval, hi, hj] using product_disequality k l
  have factors (rs : List (ProductFactor n)) :
      Product (fun x => (rs.map (fun r => r.eval (substitute p x))).prod) := by
    induction rs with
    | nil => exact product_constant m 1
    | cons r rs ih => exact (factor r).mul ih
  rcases hf with rfl | ⟨c, hc, rs, rfl⟩
  · exact product_zero m
  · exact (factors rs).scale c

variable {l m n : ℕ}

def word (p : (Fin m ⊕ Fin n) ≃ Fin l) (x : Fin m → Bool) (y : Fin n → Bool) :
    Fin l → Bool := fun j => Sum.elim x y (p.symm j)

@[simp] theorem word_left (p : (Fin m ⊕ Fin n) ≃ Fin l)
    (x : Fin m → Bool) (y : Fin n → Bool) (j : Fin m) : word p x y (p (.inl j)) = x j := by
  simp [word]
@[simp] theorem word_right (p : (Fin m ⊕ Fin n) ≃ Fin l)
    (x : Fin m → Bool) (y : Fin n → Bool) (j : Fin n) : word p x y (p (.inr j)) = y j := by
  simp [word]

theorem word_affine_left (p : (Fin m ⊕ Fin n) ≃ Fin l) (y : Fin n → Bool) :
    IsAffineMap (fun x => word p x y) := by
  intro x z
  funext j
  cases h : p.symm j with
  | inl i => simp [word, h, AffinePhase.xor, origin]
  | inr i => cases hy : y i <;> simp [word, h, AffinePhase.xor, hy]

theorem word_affine_right (p : (Fin m ⊕ Fin n) ≃ Fin l) (x : Fin m → Bool) :
    IsAffineMap (fun y => word p x y) := by
  intro y z
  funext j
  cases h : p.symm j with
  | inl i => cases hx : x i <;> simp [word, h, AffinePhase.xor, hx]
  | inr i => simp [word, h, AffinePhase.xor, origin]

def tensor (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n) :
    Signature AlgebraicComplex (m+n) := Tensor.reindex finSumFinEquiv (Tensor.tensor f g)

theorem affine_left (p : (Fin m ⊕ Fin n) ≃ Fin l)
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n} (hg : g≠0)
    (h : Affine (Tensor.reindex p (Tensor.tensor f g))) : Affine f := by
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hg
  change g y≠0 at hy
  have hs := (h.precompose (fun x => word p x y) (word_affine_left p y)).scale (g y)⁻¹
  convert hs using 1
  funext x
  simp only [Tensor.reindex, Tensor.tensor, word_left, word_right]
  change f x = (g y)⁻¹ * (f x * g y)
  field_simp

theorem affine_right (p : (Fin m ⊕ Fin n) ≃ Fin l)
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n} (hf : f≠0)
    (h : Affine (Tensor.reindex p (Tensor.tensor f g))) : Affine g := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  change f x≠0 at hx
  have hs := (h.precompose (fun y => word p x y) (word_affine_right p x)).scale (f x)⁻¹
  convert hs using 1
  funext y
  simp only [Tensor.reindex, Tensor.tensor, word_left, word_right]
  change g y = (f x)⁻¹ * (f x * g y)
  rw [←mul_assoc, inv_mul_cancel₀ hx, one_mul]

theorem product_left (p : (Fin m ⊕ Fin n) ≃ Fin l)
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n} (hg : g≠0)
    (h : Product (Tensor.reindex p (Tensor.tensor f g))) : Product f := by
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hg
  change g y≠0 at hy
  let q : Fin l → Bool ⊕ Fin m := fun j => Sum.elim Sum.inr (fun k => Sum.inl (y k)) (p.symm j)
  have he (x : Fin m → Bool) : substitute q x = word p x y := by
    funext j
    cases hq : p.symm j <;> simp [substitute, q, word, hq]
  have hs := (product_substitute q h).scale (g y)⁻¹
  convert hs using 1
  funext x
  rw [he]
  simp only [Tensor.reindex, Tensor.tensor, word_left, word_right]
  change f x = (g y)⁻¹ * (f x * g y)
  field_simp

theorem product_right (p : (Fin m ⊕ Fin n) ≃ Fin l)
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n} (hf : f≠0)
    (h : Product (Tensor.reindex p (Tensor.tensor f g))) : Product g := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  change f x≠0 at hx
  let q : Fin l → Bool ⊕ Fin n := fun j => Sum.elim (fun k => Sum.inl (x k)) Sum.inr (p.symm j)
  have he (y : Fin n → Bool) : substitute q y = word p x y := by
    funext j
    cases hq : p.symm j <;> simp [substitute, q, word, hq]
  have hs := (product_substitute q h).scale (f x)⁻¹
  convert hs using 1
  funext y
  rw [he]
  simp only [Tensor.reindex, Tensor.tensor, word_left, word_right]
  change g y = (f x)⁻¹ * (f x * g y)
  rw [←mul_assoc, inv_mul_cancel₀ hx, one_mul]

theorem tensor_nonzero {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n}
    (hf : f≠0) (hg : g≠0) : tensor f g≠0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  change f x≠0 at hx
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hg
  change g y≠0 at hy
  intro hz
  have hh := congrFun hz (word finSumFinEquiv x y)
  exact mul_ne_zero hx hy (by simpa only [tensor, Tensor.reindex, Tensor.tensor, word_left, word_right, Pi.zero_apply] using hh)

/-- The two witnesses can be different rows, including an individually
tractable affine/nonproduct row and an individually tractable product/nonaffine row. -/
theorem tensor_failures {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n}
    (hf : f≠0) (hg : g≠0) (ha : ¬Affine f) (hp : ¬Product g) :
    ¬Affine (tensor f g) ∧ ¬Product (tensor f g) :=
  ⟨fun h => ha (affine_left finSumFinEquiv hg h),
   fun h => hp (product_right finSumFinEquiv hf h)⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor
