import Holant.Certificates.AffineEndpoint.DiagonalForm
import Holant.Certificates.AffineReference.Source

/-! Division-free finite certificates for the diagonal normal form. Checking
these polynomial identities produces actual algebraic scale and diagonal
entries; it does not assume a realization or orbit-classification oracle. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def EndpointNormalForm (g : Signature AlgebraicComplex 4) : Prop :=
  ∃gamma t : AlgebraicComplex, gamma≠0 ∧ t≠0 ∧
    ∃h : Signature AlgebraicComplex 4, Affine h ∧ h zeroWord=1 ∧
      AffineReference.ReferenceSupport h ∧ g=gamma • diagonalAction t h

 theorem diagonal_form_of_cross_products (g h : Signature AlgebraicComplex 4)
    (hg : EndpointEven g) (hh : EndpointEven h) (h0 : h zeroWord=1)
    (p : Fin 6) (hgp : g (centralWord p)≠0) (hhp : h (centralWord p)≠0)
    (hcross : ∀i,g (centralWord i)*h (centralWord p)=g (centralWord p)*h (centralWord i))
    (hend : g oneWord*g zeroWord*h (centralWord p)^2=g (centralWord p)^2*h oneWord) :
    ∃gamma t : AlgebraicComplex,gamma≠0 ∧ t≠0 ∧ g=gamma • diagonalAction t h := by
  let gamma := g zeroWord
  let lam := g (centralWord p)/(gamma*h (centralWord p))
  have hgamma : gamma≠0 := hg.1
  have hlam : lam≠0 := div_ne_zero hgp (mul_ne_zero hgamma hhp)
  have hg0 : g zeroWord≠0 := hg.1
  obtain ⟨t,ht,he⟩ := diagonal_form_of_layers g h hg.2.2 hh.2.2 gamma lam hgamma hlam
    (by simp [gamma,h0]) (by dsimp [lam,gamma]; field_simp [hg0,hhp]; convert hend using 1 <;> ring)
    (by intro i; dsimp [lam,gamma]; field_simp [hg0,hhp]; exact hcross i)
  exact ⟨gamma,t,hgamma,ht,he⟩

 theorem EndpointNormalForm.scale {g : Signature AlgebraicComplex 4}
    (hg : EndpointNormalForm g) (c : AlgebraicComplex) (hc : c≠0) :
    EndpointNormalForm (c • g) := by
  obtain ⟨gamma,t,hgamma,ht,h,ha,h0,hs,rfl⟩ := hg
  exact ⟨c*gamma,t,mul_ne_zero hc hgamma,ht,h,ha,h0,hs,by simp [smul_smul]⟩

 theorem endpointNormalForm_scale_iff (g : Signature AlgebraicComplex 4)
    (c : AlgebraicComplex) (hc : c≠0) : EndpointNormalForm (c • g) ↔ EndpointNormalForm g := by
  constructor
  · intro h
    simpa [smul_smul,hc] using h.scale c⁻¹ (inv_ne_zero hc)
  · exact fun h => h.scale c hc

 theorem cross_products_normal_form (g h : Signature AlgebraicComplex 4)
    (hg : EndpointEven g) (hh : EndpointEven h) (ha : Affine h) (h0 : h zeroWord=1)
    (hs : AffineReference.ReferenceSupport h)
    (p : Fin 6) (hgp : g (centralWord p)≠0) (hhp : h (centralWord p)≠0)
    (hcross : ∀i,g (centralWord i)*h (centralWord p)=g (centralWord p)*h (centralWord i))
    (hend : g oneWord*g zeroWord*h (centralWord p)^2=g (centralWord p)^2*h oneWord) :
    EndpointNormalForm g := by
  obtain ⟨gamma,t,hgamma,ht,he⟩ := diagonal_form_of_cross_products g h hg hh h0 p hgp hhp hcross hend
  exact ⟨gamma,t,hgamma,ht,h,ha,h0,hs,he⟩

end
end Holant.Certificates.AffineEndpoint
