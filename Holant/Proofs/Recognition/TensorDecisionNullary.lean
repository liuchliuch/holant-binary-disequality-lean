import Holant.Proofs.Recognition.TensorDecisionNormalization
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

/-!
# Remove nullary factors without an oracle

This proof-side normalization removes every nullary factor of a nonzero tensor.
The new scalar is the value at an actual input pivot, and every surviving factor
is divided by its own pivot entry. It supplies the bounded positive-arity search
used by scalar-stable tensor classes; it is not an input to that search.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionNullary

open scoped BigOperators
open TensorDecisionNormalization

variable {K : Type*} [Field K] {n : ℕ} (D : TensorDecomposition K n)

abbrev Active := {i : Fin D.count // 0 < D.arity i}

noncomputable def order : Fin (Fintype.card (Active D)) ≃ Active D :=
  (Fintype.equivFin (Active D)).symm

noncomputable def ports :
    (Σ i : Fin (Fintype.card (Active D)), Fin (D.arity (order D i).val)) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (order D)).trans
    ((Equiv.sigmaSubtypeEquivOfSubset (fun i => Fin (D.arity i))
      (fun i => 0 < D.arity i) (fun _ j => Nat.zero_lt_of_lt j.isLt)).trans D.ports)

@[simp] theorem ports_apply (i : Fin (Fintype.card (Active D)))
    (j : Fin (D.arity (order D i).val)) :
    ports D ⟨i,j⟩ = D.ports ⟨(order D i).val,j⟩ := rfl

noncomputable def positive (pivot : Fin n → Bool) (hp : D.value pivot ≠ 0) :
    TensorDecomposition K n where
  count := Fintype.card (Active D)
  arity i := D.arity (order D i).val
  factor i y := D.factor (order D i).val y /
    D.factor (order D i).val (fun j => pivot (D.ports ⟨(order D i).val,j⟩))
  ports := ports D
  scale := Units.mk0 (D.value pivot) hp

theorem positive_arity (pivot : Fin n → Bool) (hp : D.value pivot ≠ 0)
    (i : Fin (positive D pivot hp).count) : 0 < (positive D pivot hp).arity i :=
  (order D i).property

theorem ratio_eq_one_of_nullary (pivot x : Fin n → Bool) (hp : D.value pivot ≠ 0)
    (i : Fin D.count) (hi : ¬ 0 < D.arity i) :
    D.factor i (fun j => x (D.ports ⟨i,j⟩)) /
      D.factor i (fun j => pivot (D.ports ⟨i,j⟩)) = 1 := by
  have heq : (fun j : Fin (D.arity i) => x (D.ports ⟨i,j⟩)) =
      (fun j : Fin (D.arity i) => pivot (D.ports ⟨i,j⟩)) := by
    funext j
    have hj := j.isLt
    omega
  rw [heq, div_self (factor_pivot_ne_zero D pivot hp i)]

theorem positive_value (pivot : Fin n → Bool) (hp : D.value pivot ≠ 0) :
    (positive D pivot hp).value = D.value := by
  funext x
  let ratio : Fin D.count → K := fun i =>
    D.factor i (fun j => x (D.ports ⟨i,j⟩)) /
      D.factor i (fun j => pivot (D.ports ⟨i,j⟩))
  have hactive : (∏ i : Active D, ratio i.val) = ∏ i, ratio i := by
    have h := Fintype.prod_subtype_mul_prod_subtype (fun i => 0 < D.arity i) ratio
    have hz : (∏ i : {i : Fin D.count // ¬ 0 < D.arity i}, ratio i.val) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      exact ratio_eq_one_of_nullary D pivot x hp i.val i.property
    rwa [hz, mul_one] at h
  calc
    (positive D pivot hp).value x = D.value pivot *
        ∏ i : Fin (Fintype.card (Active D)), ratio (order D i).val := rfl
    _ = D.value pivot * ∏ i : Active D, ratio i.val := by
      congr 1
      exact (order D).prod_comp (fun i : Active D => ratio i.val)
    _ = D.value pivot * ∏ i, ratio i := by rw [hactive]
    _ = D.value x := by
      simpa only [normalizedSlice_eq D pivot hp] using reconstruct D pivot hp x

/-- The only class assumption required by normalization: division by a nonzero
scalar preserves membership. No closure witness or correctness premise is hidden. -/
def DivisionClosed (C : (m : ℕ) → Signature K m → Prop) : Prop :=
  ∀ m (g : Signature K m) (c : K), c ≠ 0 → C m g → C m (fun y => g y / c)

theorem positive_mem (C : (m : ℕ) → Signature K m → Prop) (hC : DivisionClosed C)
    (hD : ∀ i, C (D.arity i) (D.factor i))
    (pivot : Fin n → Bool) (hp : D.value pivot ≠ 0)
    (i : Fin (positive D pivot hp).count) :
    C ((positive D pivot hp).arity i) ((positive D pivot hp).factor i) :=
  hC _ _ _ (factor_pivot_ne_zero D pivot hp (order D i).val) (hD (order D i).val)

end Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionNullary
