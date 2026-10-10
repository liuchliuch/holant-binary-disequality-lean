import Holant.Certificates.AffineEndpoint.WitnessSoundness
import Holant.Certificates.AffineEndpoint.AffineEndpoints

/-! Global output complement preserves the actual source normal-form class.
The changed diagonal entry and scale are explicit and nonzero. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.EightVertex.ProductAnchor Holant.Certificates.AffineReference Holant.Certificates.FourthRootOdd
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem complement_isAffineMap : IsAffineMap (@Tractable.complementWord 4) := by
  intro x y
  funext j
  simp only [Tractable.complementWord,xor_apply,origin]
  cases x j <;> cases y j <;> rfl

 theorem complement_odd : ∀x : Word 4,
    Holant.weight (Tractable.complementWord x)%2=1 ↔ Holant.weight x%2=1 := by decide +kernel

 theorem endpointEven_complement (g : Signature AlgebraicComplex 4) (hg : EndpointEven g) :
    EndpointEven (fun x => g (Tractable.complementWord x)) := by
  refine ⟨hg.2.1,hg.1,?_⟩
  intro x hx
  exact hg.2.2 _ ((complement_odd x).mpr hx)

 theorem endpointEven_complement_iff (g : Signature AlgebraicComplex 4) :
    EndpointEven (fun x => g (Tractable.complementWord x)) ↔ EndpointEven g := by
  constructor
  · intro h
    simpa only [Tractable.complementWord_involutive] using endpointEven_complement _ h
  · exact endpointEven_complement g

 theorem endpoint_pair_complement : ∀x : Word 4,
    (Tractable.complementWord x=zeroWord ∨ Tractable.complementWord x=oneWord) ↔
      x=zeroWord ∨ x=oneWord := by decide +kernel
 theorem plane_complement : ∀b : Fin 3,∀x : Word 4,OnPlane b (Tractable.complementWord x) ↔ OnPlane b x := by decide +kernel
 theorem even_complement : ∀x : Word 4,evenWord (Tractable.complementWord x)=evenWord x := by decide +kernel

 theorem referenceSupport_complement (h : Signature AlgebraicComplex 4) (hs : ReferenceSupport h) :
    ReferenceSupport (fun x => h (Tractable.complementWord x)) := by
  rcases hs with he|⟨b,hb⟩|hf
  · exact Or.inl (fun x => (he _).trans (endpoint_pair_complement x))
  · exact Or.inr (Or.inl ⟨b,fun x => (hb _).trans (plane_complement b x)⟩)
  · exact Or.inr (Or.inr (fun x => (hf _).trans (by rw [even_complement])))

 theorem referenceSupport_of_support_iff (f g : Signature AlgebraicComplex 4)
    (he : ∀x,g x≠0 ↔ f x≠0) (hf : ReferenceSupport f) : ReferenceSupport g := by
  rcases hf with hf|⟨b,hb⟩|hf
  · exact Or.inl (fun x => (he x).trans (hf x))
  · exact Or.inr (Or.inl ⟨b,fun x => (he x).trans (hb x)⟩)
  · exact Or.inr (Or.inr (fun x => (he x).trans (hf x)))

 theorem referenceSupport_one_ne_zero (h : Signature AlgebraicComplex 4) (hs : ReferenceSupport h) : h oneWord≠0 := by
  rcases hs with he|⟨b,hb⟩|hf
  · exact (he _).mpr (Or.inr rfl)
  · exact (hb _).mpr ⟨rfl,rfl⟩
  · exact (hf _).mpr (by decide)

 theorem diagonal_complement_factor (t : AlgebraicComplex) (ht : t≠0) (x : Word 4) :
    t^(Holant.weight (Tractable.complementWord x))=t^4*(t⁻¹)^(Holant.weight x) := by
  have hx : Holant.weight (Tractable.complementWord x)=4-Holant.weight x := by
    have he := Holant.weight_compl_add x
    change Holant.weight (Tractable.complementWord x)+Holant.weight x=4 at he
    omega
  rw [hx]
  simpa only [one_pow,mul_one,one_div] using row_weight_ratio t 1 ht x

 theorem EndpointNormalForm.complement {g : Signature AlgebraicComplex 4} (hg : EndpointNormalForm g) :
    EndpointNormalForm (fun x => g (Tractable.complementWord x)) := by
  obtain ⟨gamma,t,hgamma,ht,h,ha,h0,hs,rfl⟩ := hg
  have h1 : h oneWord≠0 := referenceSupport_one_ne_zero h hs
  let H : Signature AlgebraicComplex 4 := (h oneWord)⁻¹ • (fun x => h (Tractable.complementWord x))
  have hH : Affine H := (ha.precompose _ complement_isAffineMap).scale _
  have hHs : ReferenceSupport H := referenceSupport_of_support_iff _ H (fun x =>
    ⟨fun hx => (mul_ne_zero_iff.mp hx).2,fun hx => mul_ne_zero (inv_ne_zero h1) hx⟩)
      (referenceSupport_complement h hs)
  refine ⟨gamma*t^4*h oneWord,t⁻¹,mul_ne_zero (mul_ne_zero hgamma (pow_ne_zero 4 ht)) h1,
    inv_ne_zero ht,H,hH,?_,hHs,?_⟩
  · exact inv_mul_cancel₀ h1
  · funext x
    simp only [Pi.smul_apply,smul_eq_mul,diagonalAction_apply,diagonal_complement_factor t ht,H]
    field_simp [h1]

 theorem endpointNormalForm_complement_iff (g : Signature AlgebraicComplex 4) :
    EndpointNormalForm (fun x => g (Tractable.complementWord x)) ↔ EndpointNormalForm g := by
  constructor
  · intro h
    simpa only [Tractable.complementWord_involutive] using h.complement
  · exact EndpointNormalForm.complement

end
end Holant.Certificates.AffineEndpoint
