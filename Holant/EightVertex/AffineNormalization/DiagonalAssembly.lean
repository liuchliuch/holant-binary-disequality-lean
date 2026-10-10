import Holant.EightVertex.AffineNormalization.MatrixCores
import Holant.Certificates.AffineEndpoint.Source

/-! Assemble the analytic matrix-core classification with the complete A.4
certificate. The diagonal witness is constructed from the actual original U. -/
namespace Holant.EightVertex.AffineNormalization
open Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open Holant.EightVertex.ProductAnchor Holant.Certificates.AffineEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem diagonal_preserves_endpoint {a c : AlgebraicComplex} (ha : a≠0) (hc : c≠0)
    (M g : Signature AlgebraicComplex 4) (hM : EndpointEven M)
    (he : M=Signature.coordinateAction (fun _ => diagonal a c) g) : EndpointEven g := by
  have hp (x : Fin 4 → Bool) : M x=diagonalCoefficient a c x*g x := by
    rw [he]
    exact congrFun (coordinateAction_diagonal a c g) x
  refine ⟨?_,?_,?_⟩
  · intro h
    exact hM.1 ((hp _).trans (by rw [h,mul_zero]))
  · intro h
    exact hM.2.1 ((hp _).trans (by rw [h,mul_zero]))
  · intro x hx
    exact (mul_eq_zero.mp ((hp x).symm.trans (hM.2.2 x hx))).resolve_left
      (diagonalCoefficient_ne_zero ha hc x)

/-- Exact original-coordinate diagonal reconstruction, with the complete
endpoint/plane/full-even support certificate and all nonzero scales. -/
theorem affine_diagonal_reconstruction (M : Signature AlgebraicComplex 4)
    (hM : EndpointEven M) (U : InvertibleKernel)
    (hE : Affine (kernelSignature (Kernel.pullback Signature.disequality U.matrix)))
    (hF : Affine (U.symm.action M)) :
    ∃ a d gamma : AlgebraicComplex,a≠0 ∧ d≠0 ∧ gamma≠0 ∧
      ∃ h : Signature AlgebraicComplex 4,Affine h ∧ h zeroWord=1 ∧
        Holant.Certificates.AffineReference.ReferenceSupport h ∧
        M=gamma • Signature.coordinateAction (fun _ => diagonalKernel a d) h := by
  obtain ⟨a,c,ha,hc,K,hK,hU⟩ := affine_matrix_core U hE
  let f := U.symm.action M
  let g := Signature.coordinateAction (fun _ => K) f
  have he : M=Signature.coordinateAction (fun _ => diagonal a c) g := by
    dsimp only [g]
    rw [Signature.coordinateAction_comp]
    rw [←hU]
    exact (U.action_symm_action M).symm
  have hg := diagonal_preserves_endpoint ha hc M g hM he
  have hfn : f≠0 := by
    intro hf
    exact hg.1 (by simp [g,hf])
  obtain ⟨gamma,t,hgamma,ht,h,haff,h0,hsupp,hgform⟩ :=
    source_A4_normal_form f hF hfn K hK hg.2.2 (mul_ne_zero hg.1 hg.2.1)
  refine ⟨a,c*t,gamma,ha,mul_ne_zero hc ht,hgamma,h,haff,h0,hsupp,?_⟩
  rw [he]
  change Signature.coordinateAction (fun _ => diagonal a c) g = _
  change g=gamma • diagonalAction t h at hgform
  rw [hgform,coordinateAction_scale,diagonalAction,Signature.coordinateAction_comp]
  congr 2
  funext j x y
  cases x <;> cases y <;> simp [Kernel.mul_apply,diagonal,diagonalKernel]

def diagonalBasis (a d : AlgebraicComplex) (ha : a≠0) (hd : d≠0) : InvertibleKernel where
  matrix := diagonalKernel a d
  inverse := diagonalKernel a⁻¹ d⁻¹
  matrix_inverse := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul_apply,diagonalKernel,Signature.equality,ha,hd]
  inverse_matrix := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul_apply,diagonalKernel,Signature.equality,ha,hd]

theorem diagonal_pullback (a d : AlgebraicComplex) :
    Kernel.pullback Signature.disequality (diagonalKernel a d) =
      fun x y => (a*d)*Signature.disequality x y := by
  funext x y
  cases x <;> cases y <;>
    simp [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,diagonalKernel,Signature.disequality,mul_comm]

theorem reference_support_scale {h : Signature AlgebraicComplex 4}
    (hs : Holant.Certificates.AffineReference.ReferenceSupport h)
    (c : AlgebraicComplex) (hc : c≠0) :
    Holant.Certificates.AffineReference.ReferenceSupport (c • h) := by
  rcases hs with he|⟨b,hb⟩|hf
  · left; intro x; simpa [hc] using he x
  · right; left; exact ⟨b,fun x => by simpa [hc] using hb x⟩
  · right; right; intro x; simpa [hc] using hf x

end
end Holant.EightVertex.AffineNormalization
