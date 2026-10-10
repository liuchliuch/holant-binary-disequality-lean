import Holant.Tensor

/-! Sum-of-entries partition functions and factorization under tensor products. -/

namespace Holant.Tensor

variable {K ι κ : Type*}

/-- Sum over all Boolean assignments, with every assignment counted once. -/
noncomputable def total [Fintype ι] [AddCommMonoid K] (f : Tensor K ι) : K := by
  classical
  exact ∑ x : ι → Bool, f x

/-- An explicit port bijection does not change the fully summed tensor. -/
theorem total_reindex [Fintype ι] [Fintype κ] [AddCommMonoid K]
    (e : ι ≃ κ) (f : Tensor K ι) : total (reindex e f) = total f := by
  classical
  exact Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool)) _ _ (fun _ => rfl)

/-- Independent components multiply, derived from the finite assignment sum. -/
theorem total_tensor [Fintype ι] [Fintype κ] [Semiring K]
    (f : Tensor K ι) (g : Tensor K κ) : total (tensor f g) = total f * total g := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let : DecidableEq κ := Classical.decEq κ
  let : DecidableEq (ι ⊕ κ) := Classical.decEq (ι ⊕ κ)
  unfold total
  calc
    (∑ x : ι ⊕ κ → Bool, tensor f g x) =
        ∑ p : (ι → Bool) × (κ → Bool), f p.1 * g p.2 :=
      Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι κ Bool) _ _ (fun _ => rfl)
    _ = (∑ x : ι → Bool, f x) * ∑ y : κ → Bool, g y := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]

end Holant.Tensor
