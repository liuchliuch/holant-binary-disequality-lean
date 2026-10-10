import Holant.Marked.Monomial
import Holant.OrderedTensor

/-! The support obstruction for a product of nonsingular monomial binaries. -/
namespace Holant.Certificates.NormalizedDihedralQ6

open Holant.Marked Holant.Tractable
noncomputable section

/-- Number of nonzero coefficients, retaining all ordered Boolean assignments. -/
def coefficientSupportCard {K ι : Type*} [Zero K] [DecidableEq ι] [Fintype ι]
    (f : Tensor K ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => f x ≠ 0).card

/-- The cardinal is the usual filtered finite set, independent of decision instances. -/
theorem coefficientSupportCard_eq_filter {K ι : Type*} [Zero K] [DecidableEq ι]
    [Fintype ι] (f : Tensor K ι) [DecidablePred (fun x => f x ≠ 0)] :
    coefficientSupportCard f = (Finset.univ.filter fun x => f x ≠ 0).card := by
  classical
  unfold coefficientSupportCard
  congr 1
  ext x
  simp

/-- Port bijections preserve the number of actual nonzero coefficients. -/
theorem coefficientSupportCard_reindex {K ι κ : Type*} [Zero K]
    [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : Tensor K ι) :
    coefficientSupportCard (Tensor.reindex e f) = coefficientSupportCard f := by
  classical
  unfold coefficientSupportCard
  apply Finset.card_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool))
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- Two independent nonsingular Boolean monomial factors have four coefficients. -/
theorem monomial_tensor_support_four {L R : Mat}
    (hL : IsMonomial L) (hR : IsMonomial R) :
    coefficientSupportCard (Signature.tensor (kernelSignature L) (kernelSignature R)) = 4 := by
  classical
  obtain ⟨p, w, hw, rfl⟩ := hL
  obtain ⟨q, v, hv, rfl⟩ := hR
  calc
    coefficientSupportCard
        (Signature.tensor (kernelSignature (monomial p w))
          (kernelSignature (monomial q v))) =
        (Finset.univ.filter fun x : Fin 4 → Bool =>
          x 1 = Bool.xor (x 0) p ∧ x 3 = Bool.xor (x 2) q).card := by
      unfold coefficientSupportCard
      congr 1
      ext x
      simp [Signature.tensor_apply, kernelSignature, monomial, hw, hv, and_comm]
    _ = 4 := by cases p <;> cases q <;> decide

/-- The four-coefficient obstruction survives any ordering of the four ports. -/
theorem monomial_tensor_reindex_support_four {L R : Mat}
    (hL : IsMonomial L) (hR : IsMonomial R) (e : Equiv.Perm (Fin 4)) :
    coefficientSupportCard
      (Tensor.reindex e (Signature.tensor (kernelSignature L) (kernelSignature R))) = 4 := by
  rw [coefficientSupportCard_reindex]
  exact monomial_tensor_support_four hL hR

end
end Holant.Certificates.NormalizedDihedralQ6
