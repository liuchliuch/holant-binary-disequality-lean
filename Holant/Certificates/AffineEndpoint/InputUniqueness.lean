import Holant.Certificates.AffineEndpoint.InputModel
import Holant.Certificates.AffineEndpoint.PhaseUniqueness
import Holant.Certificates.AffineEndpoint.SupportCatalogCounts

/-! The canonical input codes are distinct actual normalized affine
signatures, not merely a covering list of 36,720 parameters. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase SupportCatalog
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

 theorem inputSignature_injective : Function.Injective inputSignature := by
  rintro ⟨s,c⟩ ⟨t,d⟩ he
  have hs : supportWords s=supportWords t := by
    ext x
    rw [←inputSignature_support ⟨s,c⟩ x,←inputSignature_support ⟨t,d⟩ x,he]
  have hst := supportWords_injective hs
  subst t
  have hv : phaseValue (phaseDecode (supportDim s) c)=phaseValue (phaseDecode (supportDim s) d) := by
    funext y
    have hy := congrFun he (supportChart s y)
    have hsys : (supportSystem s).Holds (supportChart s y) :=
      (supportSystem_holds s _).mpr (supportChart_mem s y)
    simpa only [inputSignature,chartSignature,if_pos hsys,coordinates_chart] using hy
  have hp := phaseValue_injective_small (supportDim s) (supportDim_le_four s) hv
  have hc := phaseDecode_injective_small (supportDim s) (supportDim_le_four s) hp
  subst d
  rfl

 def normalizedAffineSet : Set (Signature AlgebraicComplex 4) :=
  {f | Affine f ∧ f≠0 ∧ CanonicalNormalized f}

 theorem normalizedAffineSet_eq_range : normalizedAffineSet=Set.range inputSignature := by
  ext f
  constructor
  · rintro ⟨hf,hn,h0⟩
    obtain ⟨c,hc⟩ := normalized_input_coverage f hf hn h0
    exact ⟨c,hc.symm⟩
  · rintro ⟨c,rfl⟩
    exact ⟨inputSignature_affine c,inputSignature_ne_zero c,inputSignature_normalized c⟩

 theorem normalized_affine_count : normalizedAffineSet.ncard=36720 := by
  rw [normalizedAffineSet_eq_range,Set.ncard_range_of_injective inputSignature_injective]
  rw [Nat.card_eq_fintype_card]
  exact input_code_card

 def inputDimensionEquiv (d : Nat) :
    ({s : SupportIndex // supportDim s=d} × Fin (phaseCodeCount d)) ≃
      {c : InputCode // supportDim c.1=d} where
  toFun p := ⟨⟨p.1.val,Fin.cast (congrArg phaseCodeCount p.1.property.symm) p.2⟩,p.1.property⟩
  invFun c := ⟨⟨c.val.1,c.property⟩,Fin.cast (congrArg phaseCodeCount c.property) c.val.2⟩
  left_inv := by rintro ⟨⟨s,hs⟩,c⟩; cases hs; rfl
  right_inv := by rintro ⟨⟨s,c⟩,hs⟩; cases hs; rfl

 theorem input_dimension_card (d : Nat) :
    Fintype.card {c : InputCode // supportDim c.1=d}=
      (Finset.univ.filter (fun s : SupportIndex => supportDim s=d)).card*phaseCodeCount d := by
  rw [←Fintype.card_congr (inputDimensionEquiv d),Fintype.card_prod,Fintype.card_fin,Fintype.card_subtype]

 theorem normalized_input_dimension_counts :
    Fintype.card {c : InputCode // supportDim c.1=0}=16 ∧
    Fintype.card {c : InputCode // supportDim c.1=1}=480 ∧
    Fintype.card {c : InputCode // supportDim c.1=2}=4480 ∧
    Fintype.card {c : InputCode // supportDim c.1=3}=15360 ∧
    Fintype.card {c : InputCode // supportDim c.1=4}=16384 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := support_dimension_counts
  obtain ⟨p0,p1,p2,p3,p4⟩ := phase_code_counts
  simp only [input_dimension_card,h0,h1,h2,h3,h4,p0,p1,p2,p3,p4]
  decide

end
end Holant.Certificates.AffineEndpoint
