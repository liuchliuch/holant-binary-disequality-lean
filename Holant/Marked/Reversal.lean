import Holant.Marked.Dictionary

/-! The actual weighted reversal also preserves the displayed root-of-unity
sector group. For A the shifted reflection phase uses eta^{-2}, and its root
membership follows from eta^{2m}=1 rather than an extra assumption. -/
namespace Holant.Marked
open Tractable
noncomputable section

def reverseTransfer (U : InvertibleKernel) (T : Mat) : Mat :=
  Kernel.mul (Kernel.mul (sectorEdgeInverse U) (Kernel.transpose T)) (sectorEdge U)

theorem reverseTransfer_scale (U : InvertibleKernel) (T : Mat) (c : Scalar) :
    reverseTransfer U (scale c T) = scale c (reverseTransfer U T) := by
  change Kernel.mul (Kernel.mul _ (scale c (Kernel.transpose T))) _ = _
  rw [scale_mul_right, scale_mul_left]
  rfl

theorem reverseTransfer_projective (U : InvertibleKernel) {T V : Mat}
    (h : ProjectivelyEqual T V) :
    ProjectivelyEqual (reverseTransfer U T) (reverseTransfer U V) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, hc, reverseTransfer_scale U V c⟩

theorem reverseM_R {t : Scalar} (ht : t ≠ 0) :
    reverseTransfer InvertibleKernel.identity (R t) = scale t (R t⁻¹) := by
  change Kernel.mul (Kernel.mul _ (Kernel.transpose (R t))) _ = _
  rw [edgeInverseM, show sectorEdge InvertibleKernel.identity = _ from edgeM]
  funext a b
  cases a <;> cases b <;>
    simp [R, diagonalKernel, Kernel.mul_apply, Kernel.transpose, Signature.disequality, scale, ht]

theorem reverseM_S (t : Scalar) :
    reverseTransfer InvertibleKernel.identity (S t) = S t := by
  change Kernel.mul (Kernel.mul _ (Kernel.transpose (S t))) _ = _
  rw [edgeInverseM, show sectorEdge InvertibleKernel.identity = _ from edgeM]
  funext a b
  cases a <;> cases b <;>
    simp [R, S, diagonalKernel, Kernel.mul_apply, Kernel.transpose, Signature.disequality]

theorem reverseB (T : Mat) : reverseTransfer basisB T = Kernel.transpose T := by
  unfold reverseTransfer
  rw [edgeInverseB, show sectorEdge basisB = _ from edgeB,
    scale_mul_left, Kernel.equality_mul, scale_mul_left, scale_mul_right, Kernel.mul_equality]
  funext a b
  simp only [scale]
  ring_nf
  rw [imaginaryUnit_sq]
  ring

theorem transpose_R (t : Scalar) : Kernel.transpose (R t) = R t := by
  funext a b
  cases a <;> cases b <;> simp [R, Kernel.transpose, diagonalKernel]

theorem transpose_S {t : Scalar} (ht : t ≠ 0) :
    Kernel.transpose (S t) = scale t (S t⁻¹) := by
  funext a b
  cases a <;> cases b <;>
    simp [R, S, diagonalKernel, Kernel.mul_apply, Kernel.transpose, Signature.disequality, scale, ht]

theorem reverseA {s eta : Scalar} (hs : s ≠ 0) (hsq : s ^ 2 = eta⁻¹) (T : Mat) :
    reverseTransfer (basisA s hs) T =
      Kernel.mul (Kernel.mul (diagonalKernel 1 (-eta)) (Kernel.transpose T))
        (diagonalKernel 1 (-eta⁻¹)) := by
  unfold reverseTransfer
  rw [edgeInverseA_eta hs hsq, show sectorEdge (basisA s hs) = _ from edgeA_eta hsq,
    scale_mul_left, scale_mul_left, scale_mul_right]
  funext a b
  simp only [scale]
  ring

theorem reverseA_R {s eta : Scalar} (hs : s ≠ 0) (heta : eta ≠ 0)
    (hsq : s ^ 2 = eta⁻¹) (t : Scalar) :
    reverseTransfer (basisA s hs) (R t) = R t := by
  rw [reverseA hs hsq]
  funext a b
  cases a <;> cases b <;>
    simp [R, diagonalKernel, Kernel.mul_apply, Kernel.transpose] <;> field_simp

theorem reverseA_S {s eta t : Scalar} (hs : s ≠ 0) (heta : eta ≠ 0)
    (hsq : s ^ 2 = eta⁻¹) (ht : t ≠ 0) :
    reverseTransfer (basisA s hs) (S t) =
      scale (-eta * t) (S (eta⁻¹ ^ 2 / t)) := by
  rw [reverseA hs hsq]
  funext a b
  cases a <;> cases b <;>
    simp [R, S, diagonalKernel, Kernel.mul_apply, Kernel.transpose, Signature.disequality, scale] <;>
    field_simp

theorem Roots.inverse_square {m : ℕ} {eta : Scalar} (h : Roots (2 * m) eta) :
    Roots m (eta⁻¹ ^ 2) := by
  unfold Roots at *
  rw [← pow_mul, inv_pow, h, inv_one]

namespace Parameters
variable {m : ℕ}

theorem reversal_mem (P : Parameters m) {T : Mat} (hT : T ∈ groupM m) :
    reverseTransfer P.basis T ∈ groupM m := by
  obtain ⟨t, ht, h | h⟩ := hT
  · cases P with
    | M hm =>
      refine ⟨t⁻¹, ht.inv, Or.inl ?_⟩
      exact (reverseTransfer_projective _ h).trans ⟨t, ht.ne_zero (by omega),
        reverseM_R (ht.ne_zero (by omega))⟩
    | B hm =>
      refine ⟨t, ht, Or.inl ?_⟩
      simpa only [basis, reverseB, transpose_R] using reverseTransfer_projective basisB h
    | A hm he eta s hr hn hs =>
      refine ⟨t, ht, Or.inl ?_⟩
      simpa only [basis, reverseA_R _ (hr.ne_zero (by omega)) hs] using
        reverseTransfer_projective (basisA s (square_root_ne_zero (hr.ne_zero (by omega)) hs)) h
  · cases P with
    | M hm =>
      refine ⟨t, ht, Or.inr ?_⟩
      simpa only [basis, reverseM_S] using reverseTransfer_projective InvertibleKernel.identity h
    | B hm =>
      refine ⟨t⁻¹, ht.inv, Or.inr ?_⟩
      exact (reverseTransfer_projective _ h).trans ⟨t, ht.ne_zero (by omega),
        by rw [basis, reverseB, transpose_S (ht.ne_zero (by omega))]⟩
    | A hm he eta s hr hn hs =>
      refine ⟨eta⁻¹ ^ 2 / t, hr.inverse_square.div ht, Or.inr ?_⟩
      exact (reverseTransfer_projective _ h).trans ⟨-eta * t,
        mul_ne_zero (neg_ne_zero.mpr (hr.ne_zero (by omega))) (ht.ne_zero (by omega)),
        reverseA_S (square_root_ne_zero (hr.ne_zero (by omega)) hs)
          (hr.ne_zero (by omega)) hs (ht.ne_zero (by omega))⟩

/-- Reversing a fixed actual marked-sector binary keeps its transfer in the
complete source group, while transport still uses the actual transposed table. -/
theorem actual_reversal_mem (P : Parameters m) (B : Mat)
    (hB : sectorTransfer P.basis B ∈ groupM m) :
    sectorTransfer P.basis (Kernel.transpose B) ∈ groupM m := by
  rw [sectorTransfer_reversal]
  exact P.reversal_mem hB

end Parameters
end
end Holant.Marked
