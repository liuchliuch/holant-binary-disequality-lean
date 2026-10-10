import Holant.Certificates.AffineEndpoint.BaseTransform

/-! Arbitrary nonzero affine inputs reduce to the canonical finite family by
an actual algebraic scalar. This permits the literal fourth-root core transports
without imposing a new normalization hypothesis after the input phase twist. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase SupportCatalog
open Holant.EightVertex.ProductAnchor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem scaled_input_coverage (f : Signature AlgebraicComplex 4) (hf : Affine f) (hn : f≠0) :
    ∃a : AlgebraicComplex,a≠0 ∧ ∃c : InputCode,f=a • inputSignature c := by
  obtain ⟨s,hs⟩ := affine_support_coverage f hf hn
  let a := f (supportOrigin s)
  have ha : a≠0 := (hs _).mpr (supportOrigin_mem s)
  let g : Signature AlgebraicComplex 4 := a⁻¹ • f
  have hg : Affine g := hf.scale _
  have hgs (x : Word 4) : g x≠0 ↔ (supportSystem s).Holds x := by
    change a⁻¹*f x≠0 ↔ _
    exact (show a⁻¹*f x≠0 ↔ f x≠0 from
      ⟨fun h => (mul_ne_zero_iff.mp h).2,fun h => mul_ne_zero (inv_ne_zero ha) h⟩).trans
        ((hs x).trans (supportSystem_holds s x).symm)
  have hg0 : g (supportChart s (origin (supportDim s)))=1 := by
    rw [chart_origin]
    exact inv_mul_cancel₀ ha
  obtain ⟨c,hc⟩ := chart_phase_coverage (supportSystem s) (supportChart s) (supportCoordinates s)
    (supportChart_affine s) (fun y => (supportSystem_holds s _).mpr (supportChart_mem s y))
    (fun x hx => (chart_coordinates_iff s x).mpr ((supportSystem_holds s x).mp hx)) g hg hgs hg0
  refine ⟨a,ha,⟨s,c⟩,?_⟩
  have hcg : inputSignature ⟨s,c⟩=g := hc.symm
  rw [hcg]
  funext x
  exact (mul_inv_cancel_left₀ ha (f x)).symm

 theorem coordinateAction_scale {R : Type*} [CommSemiring R] {n : Nat}
    (L : Fin n → Bool → Bool → R) (a : R) (f : Signature R n) :
    Signature.coordinateAction L (a • f)=a • Signature.coordinateAction L f := by
  funext x
  simp only [Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

 theorem base_family_normal_form (b : Bool)
    (hcovered : ∀c : InputCode,∃w,BaseWitnessCheck c.1 c.2.val b w)
    (f : Signature AlgebraicComplex 4) (hf : Affine f) (hn : f≠0)
    (hg : EndpointEven (Signature.coordinateAction (fun _ => coreMatrix (numberedCore (baseCore b))) f)) :
    EndpointNormalForm (Signature.coordinateAction (fun _ => coreMatrix (numberedCore (baseCore b))) f) := by
  obtain ⟨a,ha,c,rfl⟩ := scaled_input_coverage f hf hn
  rw [coordinateAction_scale] at hg ⊢
  have hc := (endpointEven_scale_iff _ _ ha).mp hg
  obtain ⟨w,hw⟩ := hcovered c
  exact (baseWitnessCheck_sound c b w hw hc).scale a ha

end
end Holant.Certificates.AffineEndpoint
