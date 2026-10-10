import Holant.Certificates.OctahedralSeparator.GroupMarking
import Holant.Certificates.OctahedralSeparator.GroupTable
import Holant.Certificates.OctahedralSeparator.NativeDressed

namespace Holant.Certificates.OctahedralSeparator
noncomputable section
open Holant
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false

namespace Direction

theorem mul {f : Form} {U V : Matrix Bool Bool ℂ}
    (hU : Direction f U) (hV : Direction f V) : Direction f (U*V) := by
  obtain ⟨c,hc,i,rfl⟩ := hU
  obtain ⟨d,hd,j,rfl⟩ := hV
  refine ⟨c*d*embed (productScale i j),mul_ne_zero (mul_ne_zero hc hd)
    (embed_ne_zero (productScale_nonzero i j)),productIndex i j,?_⟩
  rw [Matrix.smul_mul,Matrix.mul_smul,← complexMatrix_mm,← theta_mm,
    standard_product,theta_ms,complexMatrix_ms]
  simp [smul_smul,mul_assoc]

end Direction

/-- The physical transfer of a binary vertex is its right-X matrix. -/
def nativeTransfer (U : Native.Binary) : Matrix Bool Bool ℂ :=
  Matrix.of (Kernel.mul U Signature.disequality)

theorem nativeTransfer_pairVertex (K : Native.Binary) :
    nativeTransfer (Native.pairVertex K) = Matrix.of X * Matrix.of K := by
  ext a b
  cases a <;> cases b <;> simp [nativeTransfer,Native.pairVertex,Kernel.mul,
    Matrix.mul_apply,X,Signature.disequality]

theorem nativeTransfer_legVertex (L : Native.Binary) :
    nativeTransfer (Native.legVertex L) = Matrix.of L := by
  ext a b
  simp [nativeTransfer,Native.legVertex,Kernel.mul_disequality]

/-- Pair vertices for any marked direction are themselves permitted group transfers. -/
theorem pairVertex_available {f : Form} {K : Native.Binary} (hK : Direction f (Matrix.of K)) :
    Direction f (nativeTransfer (Native.pairVertex K)) := by
  rw [nativeTransfer_pairVertex]
  exact (direction_X f).mul hK

theorem legVertex_available {f : Form} {L : Native.Binary} (hL : Direction f (Matrix.of L)) :
    Direction f (nativeTransfer (Native.legVertex L)) := by
  rwa [nativeTransfer_legVertex]

/-- Resource availability against an ambient family's actual transfer criterion. -/
theorem pairVertex_mem (F : SignatureFamily ℂ) (f : Form)
    (hF : ∀ U : Native.Binary, Direction f (nativeTransfer U) →
      (⟨2,Native.binarySignature U⟩ : AnySignature ℂ) ∈ F)
    {K : Native.Binary} (hK : Direction f (Matrix.of K)) :
    (⟨2,Native.binarySignature (Native.pairVertex K)⟩ : AnySignature ℂ) ∈ F :=
  hF _ (pairVertex_available hK)

theorem legVertex_mem (F : SignatureFamily ℂ) (f : Form)
    (hF : ∀ U : Native.Binary, Direction f (nativeTransfer U) →
      (⟨2,Native.binarySignature U⟩ : AnySignature ℂ) ∈ F)
    {L : Native.Binary} (hL : Direction f (Matrix.of L)) :
    (⟨2,Native.binarySignature (Native.legVertex L)⟩ : AnySignature ℂ) ∈ F :=
  hF _ (legVertex_available hL)

end
end Holant.Certificates.OctahedralSeparator
