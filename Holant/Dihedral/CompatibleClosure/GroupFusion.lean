import Holant.Dihedral.CompatibleClosure.Representatives
import Holant.Dihedral.CompatibleClosure.SelectedEdges

/-! Every actual fusion/edge reorientation in the source output remains a
nonsingular current-group monomial, with its original phase/scalar retained. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

theorem transpose_group_mem {m : ℕ} (hm : 0 < m) {T : Mat} (hT : T ∈ groupM m) :
    Kernel.transpose T ∈ groupM m := by
  obtain ⟨α,a,c,ha,hc,rfl⟩ := group_M_normal_form hm hT
  have he : Kernel.transpose (scale c (M α a)) = scale c (Kernel.transpose (M α a)) := rfl
  rw [he,transpose_M α a (ha.ne_zero hm)]
  have hroot : Roots m (exponent α a) := by cases α; exact ha; exact ha.inv
  have hs : scalar α a ≠ 0 := by cases α <;> simp [scalar,ha.ne_zero hm]
  exact (groupM_is_group hm).scale_mem _
    ((groupM_is_group hm).scale_mem _ (M_mem_group hm α hroot) _ hs) _ hc

theorem fuse_group_mem {m : ℕ} (hm : 0 < m) {C A B : Mat}
    (hC : C ∈ groupM m) (hA : A ∈ groupM m) (hB : B ∈ groupM m) :
    fuse C A B ∈ groupM m := by
  rw [fuse_eq_mul]
  exact groupM_mul hm (groupM_mul hm hA hC) hB

theorem ActualRepresentatives.binary_mem {m : ℕ} {F : SignatureFamily Scalar}
    (G : ActualRepresentatives F m) (hm : 0 < m) (γ : Bool) (t : {t : Scalar // Roots m t}) :
    G.binary γ t ∈ groupM m := by
  rw [G.normalization]
  exact (groupM_is_group hm).scale_mem _ (connection_mem_group hm γ t.property) _ (G.multiplier_ne_zero γ t)

/-- The literal new edge in PhysicalPair.spliced_factorization is an actual
current-group matrix after the computed original-edge orientation mask. -/
theorem selected_fusion_mem_group {n r m : ℕ} (hm : 0 < m)
    (p : (Fin r × Bool) ≃ Fin n) (A : Fin r → Mat) (hA : ∀ e, A e ∈ groupM m)
    (u v : Fin n) (γ : Bool) (t : {t : Scalar // Roots m t}) :
    let B := fun j => if selectMask p u v j then Kernel.transpose (A j) else A j
    fuse (M γ t.val) (B (p.symm u).1) (B (p.symm v).1) ∈ groupM m := by
  have hB (j : Fin r) : (if selectMask p u v j then Kernel.transpose (A j) else A j) ∈ groupM m := by
    split_ifs
    · exact transpose_group_mem hm (hA j)
    · exact hA j
  exact fuse_group_mem hm (M_mem_group hm γ t.property) (hB _) (hB _)

end Holant.Dihedral.CompatibleClosure
