import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenNativeM

/-! Actual identity-basis singleton presentations, including the mandatory
native edge. These row witnesses do not assert a shared target class for a
larger family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenRowBasis
open Holant Holant.Tractable

theorem native_edge_affine : Affine (kernelSignature
    (Signature.disequality : Kernel AlgebraicComplex)) := by
  let system : AffineSystem 2 := ⟨1,fun _ _ => 1,fun _ => 1⟩
  have holds (x : Fin 2 → Bool) : system.Holds x ↔ x 0 ≠ x 1 := by
    change (∀ _ : Fin 1, (∑ j : Fin 2, (1 : ZMod 2) * bitValue (ZMod 2) (x j)) = 1) ↔ _
    simp only [Fin.forall_fin_one,Fin.sum_univ_two,one_mul]
    cases x 0 <;> cases x 1 <;> decide
  convert affine_indicator system using 1
  funext x
  change Signature.disequality (x 0) (x 1) = if system.Holds x then 1 else 0
  simp only [holds]
  cases x 0 <;> cases x 1 <;> rfl

theorem native_edge_product : Product (kernelSignature
    (Signature.disequality : Kernel AlgebraicComplex)) := product_disequality 0 1

theorem singleton_affine_basis {n : ℕ} (f : Signature AlgebraicComplex n) (hf : Affine f) :
    IsCommonKBasis affineClass {⟨n,f⟩} InvertibleKernel.identity := by
  refine ⟨?_,?_⟩
  · change Affine (kernelSignature (Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix))
    simpa [InvertibleKernel.identity,Kernel.pullback] using native_edge_affine
  · rintro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    change Affine (InvertibleKernel.identity.symm.action f)
    simpa using hf

theorem singleton_product_basis {n : ℕ} (f : Signature AlgebraicComplex n) (hf : Product f) :
    IsCommonKBasis productClass {⟨n,f⟩} InvertibleKernel.identity := by
  refine ⟨?_,?_⟩
  · change Product (kernelSignature (Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix))
    simpa [InvertibleKernel.identity,Kernel.pullback] using native_edge_product
  · rintro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    change Product (InvertibleKernel.identity.symm.action f)
    simpa using hf

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenRowBasis
end
