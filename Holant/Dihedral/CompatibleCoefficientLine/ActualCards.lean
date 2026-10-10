import Holant.Dihedral.CompatibleCoefficientLine.TensorFactor

/-! The four inversion inputs are the literal source fixed physical binaries,
with their original normalization scalars and exact matching products. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

/-- Actual source cards at the first deleted pair; the designated original
residual edge is ordered first in each full matching presentation. -/
structure PhysicalFourProducts {m n r : ℕ} {F : SignatureFamily Scalar}
    (G : ActualRepresentatives F m) (t : Bool → {t : Scalar // Roots m t})
    (f : Signature Scalar (n+4)) where
  ports : Sample → (Fin r × Bool) ≃ Fin (n+2)
  factors : Sample → Fin r → Mat
  edge : Sample → Fin r
  first : ∀ i, ports i (edge i,false) = 0
  second : ∀ i, ports i (edge i,true) = 1
  originalScalar : Sample → Scalar
  originalScalar_ne_zero : ∀ i, originalScalar i ≠ 0
  actualScalar : Sample → Scalar
  actualScalar_ne_zero : ∀ i, actualScalar i ≠ 0
  actual : ∀ i, Gadget.Realizes F .disequality
    (actualScalar i • nativeCardValue f (G.binary i.1 (t i.2)))
  equation : ∀ i, actualScalar i • nativeCardValue f (G.binary i.1 (t i.2)) =
    productValue (ports i) (factors i) (originalScalar i)

/-- The analytic four-card normalization follows from the literal two-native-
wire physical card, including each fixed representative's nonzero scalar. -/
def PhysicalFourProducts.normalized {m n r : ℕ} {F : SignatureFamily Scalar}
    {G : ActualRepresentatives F m} {t : Bool → {t : Scalar // Roots m t}}
    {f : Signature Scalar (n+4)} (D : PhysicalFourProducts (r:=r) G t f) :
    FourProducts (r:=r) F (t false).val (t true).val f where
  ports := D.ports
  factors := D.factors
  edge := D.edge
  first := D.first
  second := D.second
  scalar := D.originalScalar
  scalar_ne_zero := D.originalScalar_ne_zero
  normalization i := D.actualScalar i * G.multiplier i.1 (t i.2)
  normalization_ne_zero i := mul_ne_zero (D.actualScalar_ne_zero i) (G.multiplier_ne_zero _ _)
  actual i := by
    have h := D.actual i
    rw [G.normalization,actual_close,smul_smul] at h
    rcases i with ⟨γ,b⟩
    cases b <;> simpa [phase] using h
  equation i := by
    have h := D.equation i
    rw [G.normalization,actual_close,smul_smul] at h
    rcases i with ⟨γ,b⟩
    cases b <;> simpa [phase] using h

/-- Full literal source factor alternative. The fixed binaries are actual
resources; B_e and h are only the derived analytic tensor factors. -/
theorem source_physical_genuine_factor {m n r : ℕ} (hm : 0<m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (t : Bool → {t : Scalar // Roots m t}) (ht : (t false).val ≠ (t true).val)
    (f : Signature Scalar (n+4))
    (D : PhysicalFourProducts (r:=r) (G.connections hm) t f)
    (B : Mat) (hB : IsMonomial B)
    (hline : ∀ i, ProjectivelyEqual (D.factors i (D.edge i)) B) :
    ∃ h : Signature Scalar (n+2), IsMonomial B ∧
      f = Tensor.reindex (factorPorts n) (Tensor.tensor (Tractable.kernelSignature B) h) :=
  source_genuine_tensor_factor D.normalized ht B hB hline

end Holant.Dihedral.CompatibleCoefficientLine
