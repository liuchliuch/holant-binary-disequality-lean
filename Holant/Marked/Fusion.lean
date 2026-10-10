import Holant.Marked.Basic

/-! Exact bilinear transport, physical binary fusion, and port reversal.
No projective scalar is removed from the actual binary-table identities. -/
namespace Holant.Marked
open Tractable
noncomputable section

def sectorEdge (U : InvertibleKernel) : Mat := Kernel.pullback Signature.disequality U.matrix

def sectorEdgeInverse (U : InvertibleKernel) : Mat :=
  Kernel.mul (Kernel.mul U.inverse Signature.disequality) (Kernel.transpose U.inverse)

def transport (U : InvertibleKernel) (B : Mat) : Mat :=
  Kernel.mul (Kernel.mul U.inverse B) (Kernel.transpose U.inverse)

/-- The native right transfer is BX; analytic sector coordinates conjugate it. -/
def sectorTransfer (U : InvertibleKernel) (B : Mat) : Mat :=
  conjugate U.symm (Kernel.mul B Signature.disequality)

theorem sectorEdge_symmetric (U : InvertibleKernel) :
    Kernel.transpose (sectorEdge U) = sectorEdge U := by
  simp only [sectorEdge, Kernel.pullback, Kernel.transpose_mul,
    Kernel.transpose_transpose, Kernel.transpose_disequality, Kernel.mul_assoc]

theorem sectorEdgeInverse_symmetric (U : InvertibleKernel) :
    Kernel.transpose (sectorEdgeInverse U) = sectorEdgeInverse U := by
  simp only [sectorEdgeInverse, Kernel.transpose_mul,
    Kernel.transpose_transpose, Kernel.transpose_disequality, Kernel.mul_assoc]

theorem transpose_inverse_matrix (U : InvertibleKernel) :
    Kernel.mul (Kernel.transpose U.inverse) (Kernel.transpose U.matrix) =
      Signature.equality := by
  rw [← Kernel.transpose_mul, U.matrix_inverse, Kernel.transpose_equality]

theorem transpose_matrix_inverse (U : InvertibleKernel) :
    Kernel.mul (Kernel.transpose U.matrix) (Kernel.transpose U.inverse) =
      Signature.equality := by
  rw [← Kernel.transpose_mul, U.inverse_matrix, Kernel.transpose_equality]

theorem sectorEdge_inverse (U : InvertibleKernel) :
    Kernel.mul (sectorEdge U) (sectorEdgeInverse U) = Signature.equality := by
  simp only [sectorEdge, sectorEdgeInverse, Kernel.pullback, Kernel.mul_assoc]
  rw [← Kernel.mul_assoc U.matrix U.inverse, U.matrix_inverse, Kernel.equality_mul,
    ← Kernel.mul_assoc Signature.disequality Signature.disequality,
    Kernel.disequality_mul_disequality, Kernel.equality_mul, transpose_matrix_inverse]

theorem sectorEdge_inverse_left (U : InvertibleKernel) :
    Kernel.mul (sectorEdgeInverse U) (sectorEdge U) = Signature.equality := by
  simp only [sectorEdge, sectorEdgeInverse, Kernel.pullback, Kernel.mul_assoc]
  rw [← Kernel.mul_assoc (Kernel.transpose U.inverse) (Kernel.transpose U.matrix),
    transpose_inverse_matrix, Kernel.equality_mul,
    ← Kernel.mul_assoc Signature.disequality Signature.disequality,
    Kernel.disequality_mul_disequality, Kernel.equality_mul, U.inverse_matrix]

theorem transport_mul_edge (U : InvertibleKernel) (B : Mat) :
    Kernel.mul (transport U B) (sectorEdge U) = sectorTransfer U B := by
  simp only [transport, sectorEdge, sectorTransfer, conjugate,
    InvertibleKernel.symm, Kernel.pullback, Kernel.mul_assoc]
  rw [← Kernel.mul_assoc (Kernel.transpose U.inverse) (Kernel.transpose U.matrix),
    transpose_inverse_matrix, Kernel.equality_mul]

/-- The dictionary for a literal table before passing to projective equality. -/
theorem transport_eq_transfer (U : InvertibleKernel) (B : Mat) :
    transport U B = Kernel.mul (sectorTransfer U B) (sectorEdgeInverse U) := by
  rw [← transport_mul_edge, Kernel.mul_assoc, sectorEdge_inverse, Kernel.mul_equality]

/-- Its premise says what the actual BX transfer is, rather than defining B by
its desired transformed table. The nonzero representative scalar is retained. -/
theorem transport_dictionary (U : InvertibleKernel) (B T : Mat)
    (h : ProjectivelyEqual (sectorTransfer U B) T) :
    ProjectivelyEqual (transport U B) (Kernel.mul T (sectorEdgeInverse U)) := by
  rw [transport_eq_transfer]
  exact h.mul (ProjectivelyEqual.refl _)

/-- Normal-form fusion is exact matrix multiplication with the actual edge. -/
theorem normal_form_fusion (U : InvertibleKernel) (T V : Mat) :
    Kernel.mul
      (Kernel.mul (Kernel.mul T (sectorEdgeInverse U)) (sectorEdge U))
      (Kernel.mul V (sectorEdgeInverse U)) =
        Kernel.mul (Kernel.mul T V) (sectorEdgeInverse U) := by
  rw [Kernel.mul_assoc T, sectorEdge_inverse_left, Kernel.mul_equality, Kernel.mul_assoc]

/-- This is the actual internal two-bit sum, with right binary ordered from
its internal port to its external port. -/
def fuse (E L R : Mat) : Mat := fun a b =>
  Signature.connect E (L a) (fun j => R j b)

theorem fuse_eq_mul (E L R : Mat) :
    fuse E L R = Kernel.mul (Kernel.mul L E) R := by
  funext a b
  simp only [fuse, Signature.connect, Kernel.mul_apply, Fintype.sum_bool]
  ring

/-- Transport of a physical native-X chain is a genuine weighted contraction. -/
theorem transport_fuse (U : InvertibleKernel) (B D : Mat) :
    transport U (fuse Signature.disequality B D) =
      fuse (sectorEdge U) (transport U B) (transport U D) := by
  simp only [fuse_eq_mul, transport, sectorEdge, Kernel.pullback, Kernel.mul_assoc]
  rw [← Kernel.mul_assoc (Kernel.transpose U.inverse) (Kernel.transpose U.matrix),
    transpose_inverse_matrix, Kernel.equality_mul,
    ← Kernel.mul_assoc U.matrix U.inverse, U.matrix_inverse, Kernel.equality_mul]

/-- Congruence commutes with reversal of the actual two ordered ports. -/
theorem transport_reversal (U : InvertibleKernel) (B : Mat) :
    transport U (Kernel.transpose B) = Kernel.transpose (transport U B) := by
  simp only [transport, Kernel.transpose_mul, Kernel.transpose_transpose,
    Kernel.mul_assoc]

/-- The weighted reversal transfer, including both conjugating edge factors. -/
theorem sectorTransfer_reversal (U : InvertibleKernel) (B : Mat) :
    sectorTransfer U (Kernel.transpose B) =
      Kernel.mul (Kernel.mul (sectorEdgeInverse U)
        (Kernel.transpose (sectorTransfer U B))) (sectorEdge U) := by
  rw [← transport_mul_edge, transport_reversal, transport_eq_transfer]
  rw [Kernel.transpose_mul, sectorEdgeInverse_symmetric]

/-- Exact representative scalars multiply under fusion and remain nonzero. -/
theorem actual_fusion_scalars (U : InvertibleKernel) (B D T V : Mat)
    {c d : Scalar} (hc : c ≠ 0) (hd : d ≠ 0)
    (hB : sectorTransfer U B = scale c T) (hD : sectorTransfer U D = scale d V) :
    transport U (fuse Signature.disequality B D) =
      scale (c * d) (Kernel.mul (Kernel.mul T V) (sectorEdgeInverse U)) ∧ c * d ≠ 0 := by
  refine ⟨?_, mul_ne_zero hc hd⟩
  rw [transport_fuse, fuse_eq_mul, transport_eq_transfer U B,
    transport_eq_transfer U D, hB, hD, scale_mul_left, scale_mul_left,
    scale_mul_left, scale_mul_left, scale_mul_right, normal_form_fusion]
  funext a b
  simp [scale, mul_assoc]

/-- Transport agrees with the existing two-port signature tensor action. -/
theorem transport_signature (U : InvertibleKernel) (B : Mat) :
    U.symm.action (kernelSignature B) = kernelSignature (transport U B) := by
  exact coordinateAction_kernelSignature U.inverse B


theorem edgeInverseM : sectorEdgeInverse InvertibleKernel.identity =
    Signature.disequality := by
  simp [sectorEdgeInverse, InvertibleKernel.identity]

theorem edgeInverseB : sectorEdgeInverse basisB =
    scale (imaginaryUnit / 2) Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [sectorEdgeInverse, basisB, UBInv, Kernel.mul_apply, Kernel.transpose,
      Signature.equality, Signature.disequality, scale] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem edgeInverseA {s : Scalar} (hs : s ≠ 0) :
    sectorEdgeInverse (basisA s hs) = scale (1 / 2) (diagonalKernel 1 (-(s⁻¹ ^ 2))) := by
  funext a b
  cases a <;> cases b <;>
    simp [sectorEdgeInverse, basisA, UAInv, Kernel.mul_apply, Kernel.transpose,
      Signature.disequality, diagonalKernel, scale] <;> ring

theorem edgeInverseA_eta {s eta : Scalar} (hs : s ≠ 0) (hsq : s ^ 2 = eta⁻¹) :
    sectorEdgeInverse (basisA s hs) = scale (1 / 2) (diagonalKernel 1 (-eta)) := by
  rw [edgeInverseA, inv_pow, hsq, inv_inv]

end
end Holant.Marked
