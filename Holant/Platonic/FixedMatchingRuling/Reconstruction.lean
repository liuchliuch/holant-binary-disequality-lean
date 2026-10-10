import Holant.Platonic.FixedMatchingRuling.SegreTensor
import Holant.Certificates.MatchingProductBridge.QuaternionCoordinates
import Holant.Pauli.ExoticKlein.FiberFactor

/-! Literal physical card maps and bilinear quaternion reconstruction. The
residual blocks and deleted pair are identified with the original ports by a
bijection. No reconstruction or realization assumption is used. -/
noncomputable section
namespace Holant.Platonic.FixedMatchingRuling.Physical
open Holant Holant.Certificates.MatchingProductBridge
open scoped BigOperators
open Function

/-- The source's bilinear Frobenius dual, with no complex conjugation. -/
def quaternionDual : Fin 4 → Binary :=
  ![(2 : ℂ)⁻¹ • Q0, -(2 : ℂ)⁻¹ • Q1, (2 : ℂ)⁻¹ • Q2, -(2 : ℂ)⁻¹ • Q3]

/-- Quaternion tomography uses actual matrix entries and a bilinear sum. -/
theorem quaternion_reconstruction (T : Binary) (a b : Bool) :
    (∑ i : Fin 4, quaternionDual i a b *
      (∑ c : Bool, ∑ d : Bool, quaternionBasis i c d * T c d)) = T a b := by
  cases a <;> cases b <;>
    simp [quaternionDual, quaternionBasis, Q0, Q1, Q2, Q3, Signature.equality,
      Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

variable {M P : Type*} [Fintype M]

/-- The computational-basis identification with the literal tensor power
of the two-dimensional one-port space. -/
def physicalTensorPower (n : ℕ) :
    PiTensorProduct ℂ (fun _ : Fin n => Bool → ℂ) ≃ₗ[ℂ] Signature ℂ n :=
  Segre.tensorCoordinates (fun _ => Pi.basisFun ℂ Bool)

@[simp] theorem physicalTensorPower_tprod (n : ℕ) (u : Fin n → Bool → ℂ)
    (x : Fin n → Bool) :
    physicalTensorPower n (PiTensorProduct.tprod ℂ u) x = ∏ i, u i (x i) := by
  rw [physicalTensorPower, Segre.tensorCoordinates_tprod]
  simp [Segre.product]

/-- Each physical block is its full Boolean tensor space, of dimension 2^ℓ. -/
abbrev Block (ℓ : M → ℕ) (e : M) := Tensor ℂ (Fin (ℓ e))

/-- A block coefficient index is its entire Boolean port assignment. -/
abbrev BlockAssignment (ℓ : M → ℕ) := (e : M) → Fin (ℓ e) → Bool

/-- The full standard coordinate isomorphism on the actual tensor product. -/
def blockCoordinates (ℓ : M → ℕ) :
    PiTensorProduct ℂ (Block ℓ) ≃ₗ[ℂ] (BlockAssignment ℓ → ℂ) :=
  Segre.tensorCoordinates (fun e => Pi.basisFun ℂ (Fin (ℓ e) → Bool))

@[simp] theorem blockCoordinates_tprod (ℓ : M → ℕ) (U : ∀ e, Block ℓ e)
    (x : BlockAssignment ℓ) :
    blockCoordinates ℓ (PiTensorProduct.tprod ℂ U) x = ∏ e, U e (x e) := by
  rw [blockCoordinates, Segre.tensorCoordinates_tprod]
  simp [Segre.product]

/-- Insert the two deleted bits and every block assignment on the original ports. -/
def insert (ℓ : M → ℕ) (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P)
    (a b : Bool) (x : BlockAssignment ℓ) : P → Bool := fun q =>
  Sum.elim (fun t => if t then b else a) (fun ei => x ei.1 ei.2) (p.symm q)

omit [Fintype M] in
@[simp] theorem insert_left (ℓ : M → ℕ)
    (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P) (a b t : Bool) (x : BlockAssignment ℓ) :
    insert ℓ p a b x (p (.inl t)) = if t then b else a := by simp [insert]

omit [Fintype M] in
@[simp] theorem insert_right (ℓ : M → ℕ)
    (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P) (a b : Bool) (x : BlockAssignment ℓ)
    (e : M) (i : Fin (ℓ e)) : insert ℓ p a b x (p (.inr ⟨e,i⟩)) = x e i := by
  simp [insert]

omit [Fintype M] in
/-- Splitting an original assignment and reinserting it is literally the identity. -/
theorem insert_eta (ℓ : M → ℕ) (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P)
    (x : P → Bool) :
    insert ℓ p (x (p (.inl false))) (x (p (.inl true)))
      (fun e i => x (p (.inr ⟨e,i⟩))) = x := by
  funext q
  obtain ⟨q,rfl⟩ := p.surjective q
  cases q with
  | inl t => cases t <;> simp
  | inr ei => rcases ei with ⟨e,i⟩; simp

/-- Actual card coefficients: the kernel is contracted at the ordered original pair. -/
def cardCoefficients (ℓ : M → ℕ) (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P)
    (f : Tensor ℂ P) : Binary →ₗ[ℂ] (BlockAssignment ℓ → ℂ) where
  toFun K x := ∑ a : Bool, ∑ b : Bool, K a b * f (insert ℓ p a b x)
  map_add' K L := by
    funext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c K := by
    funext x
    simp [mul_assoc, mul_add]

/-- The genuine physical card map, expressed in the residual block tensor product. -/
def cardMap (ℓ : M → ℕ) (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P)
    (f : Tensor ℂ P) : Binary →ₗ[ℂ] PiTensorProduct ℂ (Block ℓ) :=
  (blockCoordinates ℓ).symm.toLinearMap.comp (cardCoefficients ℓ p f)

@[simp] theorem blockCoordinates_cardMap (ℓ : M → ℕ)
    (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P) (f : Tensor ℂ P) (K : Binary) :
    blockCoordinates ℓ (cardMap ℓ p f K) = cardCoefficients ℓ p f K := by
  simp [cardMap]

/-- Reconstruction of every original coefficient from the four literal quaternion cards. -/
theorem card_reconstruction (ℓ : M → ℕ)
    (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P) (f : Tensor ℂ P)
    (a b : Bool) (x : BlockAssignment ℓ) :
    (∑ i : Fin 4, quaternionDual i a b *
      blockCoordinates ℓ (cardMap ℓ p f (quaternionBasis i)) x) = f (insert ℓ p a b x) := by
  simp only [blockCoordinates_cardMap]
  exact quaternion_reconstruction (fun a b => f (insert ℓ p a b x)) a b

@[simp] theorem cardMap_zero (ℓ : M → ℕ)
    (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P) : cardMap ℓ p (0 : Tensor ℂ P) = 0 := by
  apply LinearMap.ext
  intro K
  apply (blockCoordinates ℓ).injective
  ext x
  simp [cardCoefficients]

/-- No physical information is lost in the full card map. -/
theorem cardMap_eq_zero_iff (ℓ : M → ℕ)
    (p : (Bool ⊕ (e : M) × Fin (ℓ e)) ≃ P) (f : Tensor ℂ P) :
    cardMap ℓ p f = 0 ↔ f = 0 := by
  constructor
  · intro h
    funext x
    have hh := card_reconstruction ℓ p f (x (p (.inl false))) (x (p (.inl true)))
      (fun e i => x (p (.inr ⟨e,i⟩)))
    rw [insert_eta] at hh
    simpa [h] using hh.symm
  · rintro rfl
    exact cardMap_zero ℓ p

end Holant.Platonic.FixedMatchingRuling.Physical
