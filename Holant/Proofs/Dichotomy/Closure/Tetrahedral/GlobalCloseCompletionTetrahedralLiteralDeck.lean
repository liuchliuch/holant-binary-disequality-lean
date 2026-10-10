import Holant.Certificates.TetrahedralPreservers.Source

/-! Generic coefficient-only extraction from the preserved RelativeA4 proof.
No old retained-State or six-port dispatch imports are needed.
Literal four-port Frobenius cards for the internal tetrahedral case of 9.25.
The complete oriented deck retains the pair order and the two residual ports.
The adjoint below is bilinear (J Aᵀ J), never a Hermitian adjoint.
-/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open scoped BigOperators Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev PortOrder := Equiv.Perm (Fin 4)

/-- e maps the logical contracted/residual positions to original ports. -/
def relabel (e : PortOrder) (q : FourTensor) : FourTensor := Tensor.reindex e.symm q

def rawCard (q : FourTensor) (e : PortOrder) (K : BinaryMatrix) : BinaryMatrix :=
  fun c d => ∑ a : Bool, ∑ b : Bool, K a b * relabel e q ![a,b,c,d]

def BinarySafe (B : BinaryMatrix) : Prop := B = 0 ∨ groupDirection .tetrahedral B

/-- Raw and native-transfer safety coincide because X belongs to T. -/
theorem binarySafe_transfer (B : BinaryMatrix) :
    BinarySafe B ↔ B = 0 ∨ groupDirection .tetrahedral (multiply B X) := by
  rw [groupDirection_right_X_iff]
  rfl

theorem binarySafe_scale (c : ℂ) (hc : c ≠ 0) (B : BinaryMatrix) :
    BinarySafe (c • B) ↔ BinarySafe B := by
  constructor
  · rintro (hz | hg)
    · exact Or.inl ((smul_eq_zero.mp hz).resolve_left hc)
    · have h := groupDirection_smul .tetrahedral hg (inv_ne_zero hc)
      exact Or.inr (by simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h)
  · rintro (rfl | hg)
    · exact Or.inl (smul_zero _)
    · exact Or.inr (groupDirection_smul .tetrahedral hg hc)

def LiteralDeck (q : FourTensor) : Prop :=
  ∀ e : PortOrder, ∀ K : BinaryMatrix, groupDirection .tetrahedral K →
    BinarySafe (rawCard q e K)

def blockSwap : PortOrder where
  toFun := ![2,3,0,1]
  invFun := ![2,3,0,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem relabel_blocks (q : FourTensor) (x : Fin 4 → Bool) :
    relabel blockSwap q x = q ![x 2,x 3,x 0,x 1] := by
  unfold relabel Tensor.reindex
  apply congrArg q
  funext i
  fin_cases i <;> rfl

theorem relabel_relabel (q : FourTensor) (e d : PortOrder) :
    relabel d (relabel e q) = relabel (d.trans e) q := rfl

theorem deck_relabel (q : FourTensor) (h : LiteralDeck q) (e : PortOrder) :
    LiteralDeck (relabel e q) := by
  intro d K hK
  have he : rawCard (relabel e q) d K = rawCard q (d.trans e) K := by
    unfold rawCard
    rw [relabel_relabel]
  rw [he]
  exact h (d.trans e) K hK

theorem rawCard_scale_tensor (q : FourTensor) (e : PortOrder) (K : BinaryMatrix) (c : ℂ) :
    rawCard (c • q) e K = c • rawCard q e K := by
  ext a b
  simp [rawCard, relabel, Tensor.reindex, mul_add, mul_left_comm, mul_assoc]

theorem rawCard_scale_kernel (q : FourTensor) (e : PortOrder) (K : BinaryMatrix) (c : ℂ) :
    rawCard q e (c • K) = c • rawCard q e K := by
  ext a b
  simp [rawCard, mul_add, mul_assoc]

/-- Quaternion matrix multiplication is the actual ordered contraction. -/
theorem cardMatrix_action (q : FourTensor) (K : BinaryMatrix) :
    cardMatrix q *ᵥ coordinates K = coordinates (rawCard q (Equiv.refl _) K) := by
  ext i
  fin_cases i <;>
    simp [cardMatrix, rawCard, relabel, Tensor.reindex, Matrix.mulVec, dotProduct,
      coordinates_apply, quaternionCoefficient, quaternionBasis, Q0,Q1,Q2,Q3,
      Signature.equality, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Complementary original pairs give the literal Frobenius adjoint. -/
theorem cardMatrix_complement (q : FourTensor) :
    cardMatrix (relabel blockSwap q) = sharp (cardMatrix q) := by
  ext i j
  rw [sharp_apply]
  fin_cases i <;> fin_cases j <;>
    simp [cardMatrix, relabel_blocks, coordinates_apply, quaternionCoefficient,
      quaternionBasis, Q0,Q1,Q2,Q3, Signature.equality, frobeniusSigns] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem deck_oneSided (q : FourTensor) (h : LiteralDeck q) :
    OneSided Standard (cardMatrix q) := by
  intro v hv
  have hK : groupDirection .tetrahedral (assemble v) :=
    (mem_coefficientSet_iff _ v).mp hv
  have he : coordinates (assemble v) = v := coefficient_assemble v
  have ha : cardMatrix q *ᵥ v = coordinates (rawCard q (Equiv.refl _) (assemble v)) := by
    simpa only [he] using cardMatrix_action q (assemble v)
  simp only [ha]
  rcases h (Equiv.refl _) (assemble v) hK with hz | hg
  · exact Or.inl (by rw [hz, map_zero])
  · exact Or.inr ⟨_, hg, rfl⟩

/-- The finite preserver theorem's hypotheses are derived from physical tests. -/
theorem deck_twoSided (q : FourTensor) (h : LiteralDeck q) :
    TwoSided Standard (cardMatrix q) := by
  refine ⟨deck_oneSided q h, ?_⟩
  rw [← cardMatrix_complement]
  exact deck_oneSided _ (deck_relabel q h blockSwap)


end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck
