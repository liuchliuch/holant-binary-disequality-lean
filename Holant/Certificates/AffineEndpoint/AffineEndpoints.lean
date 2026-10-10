import Holant.Certificates.AffineEndpoint.AffineEndpointShapes
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase SupportCatalog
open Holant.EightVertex.ProductAnchor Holant.Certificates.AffineReference
noncomputable section
set_option backward.isDefEq.respectTransparency false
 theorem affine_endpoint_reference_support (g : Signature AlgebraicComplex 4)
    (ha : Affine g) (hg : EndpointEven g) : ReferenceSupport g := by
  have hn : g≠0 := fun h => hg.1 (congrFun h _)
  obtain ⟨s,hs⟩ := affine_support_coverage g ha hn
  have ho : ∀x,Holant.weight x%2=1→x∉supportWords s :=
    fun x hx hn => (hs x).mpr hn (hg.2.2 x hx)
  rcases endpoint_support_shapes s ((hs _).mp hg.1) ((hs _).mp hg.2.1) ho with he|⟨b,hb⟩|hf
  · exact Or.inl (fun x => (hs x).trans (he x))
  · exact Or.inr (Or.inl ⟨b,fun x => (hs x).trans (hb x)⟩)
  · exact Or.inr (Or.inr (fun x => (hs x).trans (hf x)))

 theorem affine_endpoint_normal_form (g : Signature AlgebraicComplex 4)
    (ha : Affine g) (hg : EndpointEven g) : EndpointNormalForm g := by
  let h : Signature AlgebraicComplex 4 := (g zeroWord)⁻¹ • g
  have hg0 : g zeroWord≠0 := hg.1
  have hh : Affine h := ha.scale _
  have hs : ∀x,h x≠0 ↔ g x≠0 := by
    intro x
    change (g zeroWord)⁻¹*g x≠0 ↔ g x≠0
    exact ⟨fun hx => (mul_ne_zero_iff.mp hx).2,fun hx => mul_ne_zero (inv_ne_zero hg0) hx⟩
  have hhe : EndpointEven h := by
    refine ⟨(hs _).mpr hg.1,(hs _).mpr hg.2.1,?_⟩
    intro x hx
    simp only [h,Pi.smul_apply,smul_eq_mul,hg.2.2 x hx,mul_zero]
  refine ⟨g zeroWord,1,hg.1,one_ne_zero,h,hh,?_,affine_endpoint_reference_support h hh hhe,?_⟩
  · exact inv_mul_cancel₀ hg0
  · funext x
    simp only [Pi.smul_apply,smul_eq_mul,diagonalAction_apply,one_pow,one_mul,h]
    exact (mul_inv_cancel_left₀ hg0 (g x)).symm

end
end Holant.Certificates.AffineEndpoint
