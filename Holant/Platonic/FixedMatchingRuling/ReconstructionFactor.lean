import Holant.Platonic.FixedMatchingRuling.Reconstruction

/-! A one-varying-factor ruling of actual physical cards reconstructs a proper
factorization on a displayed nontrivial partition of the original ports. -/
noncomputable section
namespace Holant.Platonic.FixedMatchingRuling.Physical
open Holant Holant.Certificates.MatchingProductBridge
open scoped BigOperators
open Function
variable {M P : Type*} [Fintype M] [DecidableEq M]

/-- Exactly the original residual ports outside the varying block. -/
abbrev FixedPorts (ℓ : M → ℕ) (e : M) := (j : {j : M // j ≠ e}) × Fin (ℓ j.val)

/-- Regroup the residual physical ports without changing or identifying any port. -/
def splitPorts (ℓ : M → ℕ) (e : M) :
    (FixedPorts ℓ e ⊕ (Bool ⊕ Fin (ℓ e))) ≃ (Bool ⊕ (j : M) × Fin (ℓ j)) where
  toFun := Sum.elim (fun ji => .inr ⟨ji.1.val,ji.2⟩)
    (Sum.elim Sum.inl (fun i => .inr ⟨e,i⟩))
  invFun := Sum.elim (fun b => .inr (.inl b))
    (fun ji => if h : ji.1 = e then .inr (.inr (h ▸ ji.2)) else .inl ⟨⟨ji.1,h⟩,ji.2⟩)
  left_inv := by
    rintro (⟨⟨j,hj⟩,i⟩ | (b | i))
    · simp [hj]
    · rfl
    · simp
  right_inv := by
    rintro (b | ⟨j,i⟩)
    · rfl
    · simp only [Sum.elim_inr]
      split_ifs with h
      · subst j
        rfl
      · rfl

/-- The fixed tensor is the literal product over the complementary blocks. -/
def fixedFactor (ℓ : M → ℕ) (e : M) (U : ∀ j, Block ℓ j) : Tensor ℂ (FixedPorts ℓ e) :=
  fun x => ∏ j : {j : M // j ≠ e}, U j.val (fun i => x ⟨j,i⟩)

/-- The second factor retains both deleted ports and the varying block, and is
reconstructed from the four literal quaternion cards using the Frobenius dual. -/
def varyingFactor (ℓ : M → ℕ) (e : M) (ψ : Binary →ₗ[ℂ] Block ℓ e) :
    Tensor ℂ (Bool ⊕ Fin (ℓ e)) := fun x =>
  ∑ i : Fin 4, quaternionDual i (x (.inl false)) (x (.inl true)) *
    ψ (quaternionBasis i) (fun j => x (.inr j))

theorem blockCoordinates_update (ℓ : M → ℕ) (e : M) (U : ∀ j, Block ℓ j)
    (v : Block ℓ e) (x : BlockAssignment ℓ) :
    blockCoordinates ℓ (PiTensorProduct.tprod ℂ (update U e v)) x =
      v (x e) * ∏ j : {j : M // j ≠ e}, U j.val (x j.val) := by
  rw [blockCoordinates_tprod, Fintype.prod_eq_mul_prod_compl e]
  simp only [update_self]
  congr 1
  rw [Finset.prod_subtype (p := fun j : M => j ≠ e) {e}ᶜ (by intro j; simp)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [update_of_ne j.property]

/-- Literal Frobenius reconstruction of an arbitrary original signature whose
actual card map has one varying tensor factor. -/
theorem reconstruction_of_ruling (ℓ : M → ℕ)
    (p : (Bool ⊕ (j : M) × Fin (ℓ j)) ≃ P) (f : Tensor ℂ P)
    (e : M) (U : ∀ j, Block ℓ j) (ψ : Binary →ₗ[ℂ] Block ℓ e)
    (hruling : ∀ K, cardMap ℓ p f K = PiTensorProduct.tprod ℂ (update U e (ψ K))) :
    f = Tensor.reindex ((splitPorts ℓ e).trans p)
      (Tensor.tensor (fixedFactor ℓ e U) (varyingFactor ℓ e ψ)) := by
  funext x
  have hrec := card_reconstruction ℓ p f (x (p (.inl false))) (x (p (.inl true)))
    (fun j i => x (p (.inr ⟨j,i⟩)))
  rw [insert_eta] at hrec
  simp_rw [hruling, blockCoordinates_update] at hrec
  rw [← hrec]
  change (∑ i : Fin 4, quaternionDual i _ _ *
      (ψ (quaternionBasis i) (fun j => x (p (.inr ⟨e,j⟩))) *
        ∏ j : {j : M // j ≠ e}, U j.val (fun k => x (p (.inr ⟨j.val,k⟩))))) =
    (∏ j : {j : M // j ≠ e}, U j.val (fun k => x (p (.inr ⟨j.val,k⟩)))) *
      ∑ i : Fin 4, quaternionDual i _ _ * ψ (quaternionBasis i) (fun j => x (p (.inr ⟨e,j⟩)))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [splitPorts]
  ring

/-- If the residual partition has at least two nonempty blocks, the fixed
complement is nonempty and the reconstructed other factor contains the deleted
pair. Hence this is a genuine proper factorization of the original tensor. -/
theorem proper_factor_of_ruling (ℓ : M → ℕ) (hℓ : ∀ e, 0 < ℓ e)
    (p : (Bool ⊕ (j : M) × Fin (ℓ j)) ≃ P) (f : Tensor ℂ P)
    (hΦ : cardMap ℓ p f ≠ 0) (hM : 2 ≤ Fintype.card M)
    (e : M) (U : ∀ j, Block ℓ j) (ψ : Binary →ₗ[ℂ] Block ℓ e)
    (hruling : ∀ K, cardMap ℓ p f K = PiTensorProduct.tprod ℂ (update U e (ψ K))) :
    Pauli.ExoticKlein.Fiber.HasProperTensorFactor f := by
  have : Nontrivial M := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨j,hj⟩ := exists_ne e
  have hn : f ≠ 0 := fun h => hΦ ((cardMap_eq_zero_iff ℓ p f).mpr h)
  apply Pauli.ExoticKlein.Fiber.factor_of_split ((splitPorts ℓ e).trans p)
    (fixedFactor ℓ e U) (varyingFactor ℓ e ψ) f _ _ hn
    (reconstruction_of_ruling ℓ p f e U ψ hruling)
  · exact Fintype.card_pos_iff.mpr ⟨⟨⟨j,hj⟩,⟨0,hℓ j⟩⟩⟩
  · exact Fintype.card_pos_iff.mpr ⟨Sum.inl false⟩

end Holant.Platonic.FixedMatchingRuling.Physical
