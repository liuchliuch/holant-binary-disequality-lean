import Holant.Projective.BoundedTorsion.Group
import Holant.OpenNetworkComposition.Closure

/-! Actual native-X gadgets supply the multiplicative closure used in
Lemma 5.2.  Projective representatives are scalar-saturated only after the
literal actual gadget has been exhibited. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {K : Type*} [Field K]

def binarySignature (B : Binary (K := K)) : Signature K 2 :=
  fun x => B (x 0) (x 1)

def ActualNonsingular (F : SignatureFamily K) (B : Binary (K := K)) : Prop :=
  Gadget.Realizes F .disequality (binarySignature B) ∧ Matrix.det B ≠ 0

/-- Literal representatives of all projective transfer classes of actual
nonsingular ordered binaries.  The transfer is exactly `B * X`. -/
def actualTransfers (F : SignatureFamily K) : Set (Binary (K := K)) :=
  {T | ∃ B, ActualNonsingular F B ∧ ∃ c : K, c ≠ 0 ∧ T = c • transfer B}

theorem binary_series_splice (B C : Binary (K := K)) :
    binarySignature (B * X * C) =
      OpenNetworkComposition.spliceTensor (binarySignature C) (binarySignature B) 0 := by
  funext x
  simp [binarySignature, OpenNetworkComposition.spliceTensor, Matrix.mul_apply,
    X, Signature.disequality, Fin.sum_univ_two, mul_add, add_mul]
  ring

theorem realizes_series {F : SignatureFamily K} {B C : Binary (K := K)}
    (hB : Gadget.Realizes F .disequality (binarySignature B))
    (hC : Gadget.Realizes F .disequality (binarySignature C)) :
    Gadget.Realizes F .disequality (binarySignature (B * X * C)) := by
  rw [binary_series_splice]
  exact OpenNetworkComposition.realizes_splice F _ _ hC hB 0

theorem det_X_ne_zero : Matrix.det (X : Binary (K := K)) ≠ 0 := by
  have h := congrArg Matrix.det (X_mul_X (K := K))
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  simp [hz] at h

theorem ActualNonsingular.series {F : SignatureFamily K} {B C : Binary (K := K)}
    (hB : ActualNonsingular F B) (hC : ActualNonsingular F C) :
    ActualNonsingular F (B * X * C) := by
  refine ⟨realizes_series hB.1 hC.1, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hB.2 det_X_ne_zero) hC.2

theorem transfer_series (B C : Binary (K := K)) :
    transfer (B * X * C) = transfer B * transfer C := by
  simp only [transfer, Matrix.mul_assoc]

theorem actualTransfers_mul {F : SignatureFamily K} {U V : Binary (K := K)}
    (hU : U ∈ actualTransfers F) (hV : V ∈ actualTransfers F) :
    U * V ∈ actualTransfers F := by
  obtain ⟨B, hB, c, hc, rfl⟩ := hU
  obtain ⟨C, hC, d, hd, rfl⟩ := hV
  refine ⟨B * X * C, hB.series hC, c * d, mul_ne_zero hc hd, ?_⟩
  rw [transfer_series, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem actualTransfers_scale {F : SignatureFamily K} {T : Binary (K := K)}
    (hT : T ∈ actualTransfers F) {c : K} (hc : c ≠ 0) :
    c • T ∈ actualTransfers F := by
  obtain ⟨B, hB, d, hd, rfl⟩ := hT
  exact ⟨B, hB, c * d, mul_ne_zero hc hd, smul_smul _ _ _⟩

/-- Source Lemma 5.2's subgroup conclusion, with no finiteness assumption.
Its further assertion that there are finitely many projective classes is not
claimed here. -/
theorem actualTransfers_projectiveMatrixGroup (F : SignatureFamily K)
    (hne : (actualTransfers F).Nonempty)
    (htorsion : ∀ B, ActualNonsingular F B → ProjectivelyFinite (transfer B)) :
    ProjectiveMatrixGroup (actualTransfers F) := by
  apply projectiveMatrixGroup_of_torsion hne
  · exact fun _ hU _ hV => actualTransfers_mul hU hV
  · exact fun _ hT _ hc => actualTransfers_scale hT hc
  · rintro T ⟨B, hB, c, hc, rfl⟩
    exact (htorsion B hB).smul hc

end
end Holant.Projective.BoundedTorsion
