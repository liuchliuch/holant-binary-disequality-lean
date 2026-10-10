import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4FullSource
import Holant.Tractable.Anchor.MatrixActions

/-! The actual ordinary X vertex excludes the local-affine branch in the
presence of both literal pins. This uses the shared inverse basis and X's
literal transformed table, not a complexity-separation assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXLocalExclusion
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
namespace T
export StableHigherCurrentOrdinaryTerminal (Test AffineTest LocalTest Obstruction pin_preprocess)
end T
namespace L
export StableHigherCurrentAnchorLocalBasis (pin common_basis_monomial)
end L
namespace E
export GlobalCloseCompletionEq4FullSource (family family_x family_pin tract_iff_test)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {H : SignatureFamily AlgebraicComplex}
variable (h0 : (⟨1,L.pin false⟩ : AnySignature AlgebraicComplex)∈H)
variable (h1 : (⟨1,L.pin true⟩ : AnySignature AlgebraicComplex)∈H)
variable (hx : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈H)

/- Monomial inverse action leaves a nonzero symmetric off-diagonal binary.
No symmetric LocalAffine binary can have such support. -/
include h0 h1 hx in
theorem not_common_local (B : InvertibleKernel) : ¬IsCommonBasis localAffineClass H B := by
  intro hb
  have hm := (L.common_basis_monomial B h0 h1 hb).2
  have ht := hb.2 _ hx
  change LocalAffine (B.symm.action (kernelSignature Signature.disequality)) at ht
  rw [InvertibleKernel.action,coordinateAction_kernelSignature] at ht
  let M := Kernel.mul (Kernel.mul B.inverse Signature.disequality) (Kernel.transpose B.inverse)
  change LocalAffine (kernelSignature M) at ht
  have sym : Kernel.transpose M=M := by
    funext x y
    cases x <;> cases y <;> simp [M,Kernel.transpose,Kernel.mul_apply,Signature.disequality] <;> ring
  have zero := (localAffine_offdiagonal_zero ht sym).1
  have det := determinant_ne_zero B.symm
  change determinant B.inverse≠0 at det
  rcases hm with ⟨h01,h10⟩|⟨h00,h11⟩
  · have hz : B.inverse false false*B.inverse true true=0 := by
      simpa [M,Kernel.mul_apply,Kernel.transpose,Signature.disequality,h01,h10] using zero
    exact det (by simp [determinant,h01,h10,hz])
  · have hz : B.inverse false true*B.inverse true false=0 := by
      simpa [M,Kernel.mul_apply,Kernel.transpose,Signature.disequality,h00,h11] using zero
    exact det (by simp [determinant,h00,h11,hz])

include h0 h1 hx in
theorem not_local_test : ¬T.LocalTest H := by
  rintro ⟨opposite,q,h⟩
  exact not_common_local h0 h1 hx _ h

/- Only common Affine and literal Product tests remain. -/
include h0 h1 hx in
theorem test_iff : T.Test H ↔ T.AffineTest H ∨ H⊆productClass := by
  unfold T.Test
  exact or_congr_right (or_iff_left (not_local_test h0 h1 hx))

include h0 h1 hx in
theorem not_common_transformable : ¬CommonTransformable localAffineClass H := by
  rintro ⟨_,B,h⟩
  exact not_common_local h0 h1 hx B h

include hx in
theorem x_preprocess :
    (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈preprocess H := by
  refine ⟨hx,by decide,?_⟩
  intro h
  have h' := congrFun h (![false,true] : Fin 2→Bool)
  norm_num [kernelSignature,Signature.disequality] at h'

section Original
open Holant.LocalDrafts.RemoteWork.StableClosureV2
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (d : GlobalCloseCompletionEq4Graph.Output G P)

theorem original_family_no_local : ¬T.LocalTest (preprocess (E.family G P d)) :=
  not_local_test (T.pin_preprocess (E.family_pin G P d false))
    (T.pin_preprocess (E.family_pin G P d true)) (x_preprocess (E.family_x G P d))

/- A strict same-family criterion reduction for the actual Eq4 source.
This does not yet assert hardness of its negative branch. -/
theorem original_tract_iff : Tract (E.family G P d) ↔
    T.AffineTest (preprocess (E.family G P d)) ∨ preprocess (E.family G P d)⊆productClass := by
  rw [E.tract_iff_test]
  exact test_iff (T.pin_preprocess (E.family_pin G P d false))
    (T.pin_preprocess (E.family_pin G P d true)) (x_preprocess (E.family_x G P d))
end Original

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXLocalExclusion
end
