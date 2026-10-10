import Holant.Proofs.Hardness.EightVertexGaugeEqualityAnchor

/-! The actual fourth-phase representative that becomes X in the canonical
dense-anchor coordinates. Its phase is −r², not necessarily −1; the original
representative multiplier remains in the exact nonzero transformed scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDenseAnchorX
open Holant Holant.Tractable Holant.Marked
open Holant.Certificates.EqualityQuaternary
open Holant.EightVertex.ProductAnchor
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

/-- Eighth-root weight gives the required actual fourth-root diagonal phase. -/
theorem selected_phase_root (r : AlgebraicComplex) (eighth : r^8=1) : Roots 4 (-(r^2)) := by
  change (-(r^2))^4=1
  calc
    _ = r^8 := by ring
    _ = 1 := eighth

private theorem normalization_phase_matrix (r u mu : AlgebraicComplex) (hr : r≠0) :
    Kernel.mul (Kernel.mul (normalizationMatrix r u) (scale mu (Holant.Marked.R (-(r^2)))))
      (Kernel.transpose (normalizationMatrix r u))=
        scale (mu*imaginaryUnit*u^2/2) Signature.disequality := by
  funext b c
  cases b <;> cases c <;>
    simp [normalizationMatrix,Holant.EightVertex.ProductAnchor.matrix,scale,Holant.Marked.R,
      diagonalKernel,Kernel.mul_apply,Kernel.transpose,Signature.disequality] <;>
    field_simp [hr] <;> ring

theorem normalization_phase_X (r u mu : AlgebraicComplex) (hr : r≠0) (hu : u≠0) (square : u^2=2*r) :
    (denseNormalization r u hr hu).action (kernelSignature (scale mu (Holant.Marked.R (-(r^2)))))=
      fun x => (mu*imaginaryUnit*r)*kernelSignature Signature.disequality x := by
  rw [InvertibleKernel.action,coordinateAction_kernelSignature]
  change kernelSignature (Kernel.mul
    (Kernel.mul (normalizationMatrix r u) (scale mu (Holant.Marked.R (-(r^2)))))
      (Kernel.transpose (normalizationMatrix r u)))=_
  rw [normalization_phase_matrix r u mu hr,square]
  funext x
  change (mu*imaginaryUnit*(2*r)/2)*kernelSignature Signature.disequality x=_
  ring

/-- The returned binary is an actual original-family graph, not a normalized
phase postulated as a supplied signature. The canonical basis sends it to the
specified scalar X with no phase or representative coefficient discarded. -/
theorem actual_scaled_X (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F 4) (r u : AlgebraicComplex)
    (hr : r≠0) (hu : u≠0) (square : u^2=2*r) (eighth : r^8=1) :
    ∃ (f : Signature AlgebraicComplex 2) (c : AlgebraicComplex),c≠0 ∧
      Gadget.Realizes F .disequality f ∧
      (denseNormalization r u hr hu).action f=
        (fun x => c*kernelSignature Signature.disequality x) := by
  let t : Holant.Marked.SupportAtlas.Phase 4 := ⟨-(r^2),selected_phase_root r eighth⟩
  let mu := reps.multiplier false t
  refine ⟨kernelSignature (reps.matrix false t),mu*imaginaryUnit*r,
    mul_ne_zero (mul_ne_zero (reps.multiplier_ne_zero false t) imaginaryUnit_ne_zero) hr,
    reps.actual false t,?_⟩
  rw [reps.normal_form]
  exact normalization_phase_X r u mu hr hu square


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBDenseAnchorX
end
