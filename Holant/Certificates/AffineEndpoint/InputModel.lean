import Holant.Certificates.AffineEndpoint.SupportCatalog
import Holant.Certificates.AffineEndpoint.ChartPhase

/-! The finite input family is derived from arbitrary genuine affine
signatures. Original port order and the least supported-word normalization are
retained throughout; chart completeness is a proved theorem. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open SupportCatalog
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev InputCode := (s : SupportIndex) × Fin (phaseCodeCount (supportDim s))

 def inputSignature (c : InputCode) : Signature AlgebraicComplex 4 :=
  chartSignature (supportSystem c.1) (supportCoordinates c.1) (phaseDecode (supportDim c.1) c.2)

 def rawInputSignature (c : InputCode) (x : Word 4) : OctahedralSeparator.Scalar :=
  if x∈supportWords c.1 then OctahedralSeparator.imag^
    ((phaseQuadratic (phaseDecode (supportDim c.1) c.2)).eval (supportCoordinates c.1 x)).val else 0

 theorem inputSignature_affine (c : InputCode) : Affine (inputSignature c) :=
  chartSignature_affine _ _ (supportCoordinates_affine c.1) _

 theorem inputSignature_support (c : InputCode) (x : Word 4) :
    inputSignature c x≠0 ↔ x∈supportWords c.1 :=
  (chartSignature_ne_zero_iff _ _ _ x).trans (supportSystem_holds c.1 x)

 theorem inputSignature_origin (c : InputCode) : inputSignature c (supportOrigin c.1)=1 := by
  have hc := coordinates_chart c.1 (origin (supportDim c.1))
  rw [chart_origin] at hc
  simp [inputSignature,chartSignature,(supportSystem_holds _ _).mpr (supportOrigin_mem c.1),hc,phaseValue_origin]

 theorem inputSignature_ne_zero (c : InputCode) : inputSignature c≠0 := by
  intro h
  have hh := inputSignature_origin c
  rw [h] at hh
  exact zero_ne_one hh

 theorem algebraicEmbed_rawInputSignature (c : InputCode) (x : Word 4) :
    algebraicEmbed (rawInputSignature c x)=inputSignature c x := by
  simp only [rawInputSignature,inputSignature,chartSignature,supportSystem_holds,phaseValue,
    fourthRootPhase]
  split_ifs <;> simp

/-- Exactly the source normalization at the lexicographically first support word. -/
 def CanonicalNormalized (f : Signature AlgebraicComplex 4) : Prop :=
  ∀a,f a≠0→(∀x,f x≠0→wordCode a≤wordCode x)→f a=1

 theorem inputSignature_normalized (c : InputCode) : CanonicalNormalized (inputSignature c) := by
  intro a ha hleast
  have h1 := hleast (supportOrigin c.1) ((inputSignature_support c _).mpr (supportOrigin_mem c.1))
  have h2 := supportOrigin_least c.1 a ((inputSignature_support c a).mp ha)
  have he : a=supportOrigin c.1 := wordCode_injective (le_antisymm h1 h2)
  rw [he,inputSignature_origin]

 theorem normalized_input_coverage (f : Signature AlgebraicComplex 4) (hf : Affine f)
    (hn : f≠0) (h0 : CanonicalNormalized f) : ∃c : InputCode,f=inputSignature c := by
  obtain ⟨s,hs⟩ := affine_support_coverage f hf hn
  have horigin : f (supportOrigin s)=1 := h0 _ ((hs _).mpr (supportOrigin_mem s))
    (fun x hx => supportOrigin_least s x ((hs x).mp hx))
  obtain ⟨c,hc⟩ := chart_phase_coverage (supportSystem s) (supportChart s) (supportCoordinates s)
    (supportChart_affine s)
    (fun y => (supportSystem_holds s _).mpr (supportChart_mem s y))
    (fun x hx => (chart_coordinates_iff s x).mpr ((supportSystem_holds s x).mp hx))
    f hf (fun x => (hs x).trans (supportSystem_holds s x).symm)
    (by simpa only [chart_origin] using horigin)
  exact ⟨⟨s,c⟩,hc⟩

 theorem input_code_card : Fintype.card InputCode=36720 := by
  simp only [InputCode,Fintype.card_sigma,Fintype.card_fin]
  decide +kernel

end
end Holant.Certificates.AffineEndpoint
