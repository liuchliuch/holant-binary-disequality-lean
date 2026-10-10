import Holant.Platonic.RankDeficientLocalization.Normalization.MarkedCards
import Holant.Certificates.RainbowOrbit.MarkedPermutations

/-! Marked normalization is lifted into actual current-group binary factors.
The conjugator is used only to prove identities, never as a graph label. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

abbrev theta := OctahedralSeparator.complexTheta
abbrev Direction := OctahedralSeparator.Direction
abbrev markMap := PlatonicBridgeInterface.Octahedral.markMap

theorem theta_transpose_corrected (f : Form) (K : Mat) :
    theta f K.transpose=theta f (markSinv f)*(theta f K).transpose*theta f (markS f) := by
  have he : (theta f K).transpose=theta f (markS f*K.transpose*markSinv f) := by
    calc
      (theta f K).transpose=(markH f).transpose*K.transpose*(markH f).transpose⁻¹ := by
        simp [theta,OctahedralSeparator.complexTheta,markH,Matrix.transpose_mul,
          Matrix.transpose_nonsing_inv,mul_assoc]
      _ = _ := conjugation_transposed_leg f K.transpose
  rw [he,←theta_mul,←theta_mul]
  congr 1
  simp only [mul_assoc,markSinv_mul_markS,mul_one]
  rw [←mul_assoc (markSinv f),markSinv_mul_markS,one_mul]

def currentDressing (f : Form) (D : DomainAction .octahedral) (L : Legs) : SixDressing where
  left := theta f D.left*(if D.swap then theta f (markSinv f) else 1)
  right := (if D.swap then theta f (markS f) else 1)*theta f D.right
  swap := D.swap
  residual := currentLegs f L

theorem currentDressing_domain (f : Form) (D : DomainAction .octahedral) (L : Legs) (K : Mat) :
    (currentDressing f D L).left*(if D.swap then (theta f K).transpose else theta f K)*
      (currentDressing f D L).right=theta f (D.apply K) := by
  cases hs : D.swap
  · simp only [currentDressing,hs,Bool.false_eq_true,if_false,mul_one,one_mul,
      DomainAction.apply,theta_mul]
  · simp only [currentDressing,hs,if_true,DomainAction.apply]
    calc
      (theta f D.left*theta f (markSinv f))*(theta f K).transpose*
          (theta f (markS f)*theta f D.right) =
        theta f D.left*(theta f (markSinv f)*(theta f K).transpose*theta f (markS f))*theta f D.right := by
          simp only [mul_assoc]
      _ = _ := by rw [←theta_transpose_corrected,←theta_mul,←theta_mul]

theorem currentDressing_directions (f : Form) (D : DomainAction .octahedral)
    (L : Legs) (hL : GroupLegs .octahedral L) :
    ∀j,Direction f ((currentDressing f D L).legs j) := by
  have hl : Direction f (currentDressing f D L).left := by
    apply OctahedralSeparator.Direction.mul (theta_direction f D.left_mem)
    cases hs : D.swap <;> simp only [hs,Bool.false_eq_true,if_false,if_true]
    · simpa only [theta_one] using theta_direction f (direction_one .octahedral)
    · exact theta_direction f (markSinv_source f)
  have hr : Direction f (currentDressing f D L).right := by
    apply OctahedralSeparator.Direction.mul _ (theta_direction f D.right_mem)
    cases hs : D.swap <;> simp only [hs,Bool.false_eq_true,if_false,if_true]
    · simpa only [theta_one] using theta_direction f (direction_one .octahedral)
    · exact theta_direction f (markS_source f)
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => currentLegs_mem f L hL k) j) j
  · exact marked_direction_transpose f hl
  · exact hr

theorem currentDressing_actualMap (f : Form) (D : DomainAction .octahedral) (L : Legs)
    (h : Signature ℂ 6) :
    actualMap ((currentDressing f D L).tensor h)=markMap f (dressedMap D L (unmarkMap f (actualMap h))) := by
  apply LinearMap.ext
  intro K
  obtain ⟨K,rfl⟩ := (thetaEquiv f).surjective K
  rw [PlatonicBridgeInterface.Octahedral.markMap_theta]
  change Signature.contract (theta f K) ((currentDressing f D L).tensor h)=_
  rw [SixDressing.card]
  change act (currentLegs f L) (Signature.contract
    ((currentDressing f D L).left*(if D.swap then (theta f K).transpose else theta f K)*
      (currentDressing f D L).right) h)=_
  rw [currentDressing_domain]
  have hundo : Signature.contract (theta f (D.apply K)) h=
      act (markLegs f) (unmarkMap f (actualMap h) (D.apply K)) := by
    change actualMap h (thetaEquiv f (D.apply K))=
      coefficientEquiv f ((coefficientEquiv f).symm (actualMap h (thetaEquiv f (D.apply K))))
    exact ((coefficientEquiv f).apply_symm_apply _).symm
  rw [hundo,currentLegs_intertwine]
  rfl

theorem mark_ancestor (f : Form) (p : Fin 6) :
    markMap f (actualMap (PlatonicDeficient.ancestor p))=
      actualMap (OctahedralSeparator.complexTensor (OctahedralSeparator.deficientAncestor f p)) := by
  calc
    markMap f (actualMap (PlatonicDeficient.ancestor p))=
        markMap f (TetrahedralBridge.sourceMap (p.castAdd 6)) :=
      congrArg (markMap f) (PlatonicDeficient.standard_low_actualMap p).symm
    _ = PlatonicBridgeInterface.Octahedral.physicalMap f (p.castAdd 24) :=
      congrArg (markMap f) (PlatonicBridgeInterface.Octahedral.low_map_eq p).symm
    _ = _ := PlatonicDeficient.physical_low_actualMap f p

/-- Actual current-coordinate normalization for every marked octahedral form.
In particular f=1 is the literal O′ case in A.24. -/
theorem marked_deficient_normalization (f : Form) (h : Signature ℂ 6)
    (hc : ∀i,MarkedCone f (actualMap h (markedRepresentative f i)))
    (hm : MixedCards (actualMap h) (markedRepresentative f))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,∃D : DomainAction .octahedral,∃L : Legs,GroupLegs .octahedral L ∧
      (currentDressing f D L).tensor h=
        OctahedralSeparator.complexTensor (OctahedralSeparator.deficientAncestor f p) ∧
      Module.finrank ℂ (actualMap h).range=2 := by
  let Φ := unmarkMap f (actualMap h)
  have hc0 := unmark_cards f (actualMap h) hc
  have hm0 := unmark_mixed f (actualMap h) hc hm
  obtain ⟨R⟩ := platonic_mixed_rainbow .octahedral (LinearEquiv.refl ℂ Mat) Φ
    (fun i => matchingCone_card .octahedral _ (hc0 i)) hm0
  obtain ⟨D,L,hL,hn,hRank⟩ := source_normalization Φ R hc0
  have hRank0 : Module.finrank ℂ Φ.range=Module.finrank ℂ (actualMap h).range := unmark_rank f _
  obtain ⟨p,hp,h2⟩ := sourceEquations_deficient .octahedral (dressedMap D L Φ) hn (by omega)
  refine ⟨p,D,L,hL,?_,by omega⟩
  apply PlatonicDeficient.actualMap_injective
  exact (currentDressing_actualMap f D L h).trans
    ((congrArg (markMap f) hp).trans (mark_ancestor f p))

end
end Holant.Platonic.RankDeficientLocalization.Normalization
