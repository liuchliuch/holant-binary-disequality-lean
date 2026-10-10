import Holant.Certificates.PlatonicBridgeInterface.OctahedralMarkedMaps

/-! Exact agreement with the literal source tensor tables and physical kernel
cards, preserving every scalar and the original current-coordinate outputs. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OctahedralSeparator (complexTensor complexMatrix)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem regular_eq_source (j : Fin 9) :
    regular j = complexTensor (OctahedralSeparator.regular j) := by
  rw [regular_eq_R]
  funext x
  obtain ⟨w,rfl⟩ := TetrahedralDeck.words_surjective x
  fin_cases j <;> fin_cases w <;>
    norm_num [R,P2,inverseQuaternion,symmetricQuaternion,conjugateQuaternion,
      normSquare,sliceVector,directionIndex,octahedralRaw,GoldenInt.eval,
      Q0,Q1,Q3,Signature.equality,TetrahedralDeck.words,
      complexTensor,OctahedralSeparator.regular,OctahedralSeparator.tensorScale,
      OctahedralSeparator.p2,OctahedralSeparator.q,OctahedralSeparator.mat,
      OctahedralSeparator.embed_mul,OctahedralSeparator.embed_add,
      OctahedralSeparator.embed_sub,OctahedralSeparator.embed_neg,
      OctahedralSeparator.embed_imag,OctahedralSeparator.embed_one,
      OctahedralSeparator.embed_zero,OctahedralSeparator.rat,
      OctahedralSeparator.embed_coeff] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem half_c_eq_source :
    (1/2 : ℂ) • C = complexTensor
      (OctahedralSeparator.tensorScale (OctahedralSeparator.rat (1/2)) OctahedralSeparator.cTensor) := by
  funext x
  simp only [complexTensor,OctahedralSeparator.tensorScale,OctahedralSeparator.cTensor,
    OctahedralSeparator.p2,OctahedralSeparator.embed_mul]
  have hq := OctahedralSeparator.complexMatrix_q 2
  have hrat : OctahedralSeparator.embed (OctahedralSeparator.rat (1/2)) = (1/2 : ℂ) := by
    norm_num [OctahedralSeparator.rat,OctahedralSeparator.embed_coeff]
  rw [hrat]
  change (1/2 : ℂ) * (Q2 (x 0) (x 3)*Q2 (x 1) (x 2)) = _
  rw [show OctahedralSeparator.embed (OctahedralSeparator.q 2 (x 0) (x 3)) = Q2 (x 0) (x 3) from congrFun (congrFun hq (x 0)) (x 3),
    show OctahedralSeparator.embed (OctahedralSeparator.q 2 (x 1) (x 2)) = Q2 (x 1) (x 2) from congrFun (congrFun hq (x 1)) (x 2)]

/-- The index4×6 is the exact four displayed frames with all six orderings. -/
theorem sourceImages_high (i : Fin 24) (k : Fin 4) :
    sourceImages (i.natAdd 6) k = complexTensor
      (OctahedralSeparator.fullImages ⟨i.val/6,by omega⟩ ⟨i.val%6,by omega⟩ k) := by
  fin_cases k
  · exact half_c_eq_source
  · change orderedTuple (i.natAdd 6) 0 = _
    rw [high_orderedTuple,regular_eq_source]
    rfl
  · change orderedTuple (i.natAdd 6) 1 = _
    rw [high_orderedTuple,regular_eq_source]
    rfl
  · change orderedTuple (i.natAdd 6) 2 = _
    rw [high_orderedTuple,regular_eq_source]
    rfl

theorem physicalMap_basis (f : Form) (i : Fin 30) (k : Fin 4) :
    physicalMap f i (complexMatrix (OctahedralSeparator.theta f (OctahedralSeparator.q k))) =
      coefficientEquiv f (sourceImages i k) := by
  rw [OctahedralSeparator.complexMatrix_theta,OctahedralSeparator.complexMatrix_q]
  change markMap f (sourceMap i) (thetaEquiv f (quaternionBasis k)) = _
  rw [markMap_theta,sourceMap_basis]

/-- Exhaustivity supplies the actual source-card hypothesis of the accepted
separator theorem. No finite-card premise is imposed on the six-port input. -/
theorem actual_full_card_map (f : Form) (h : Signature ℂ 6)
    (hn : SourceHypotheses f (actualMap h)) (hr : mapRank (actualMap h) = 4) :
    ∃ i : Fin 24, OctahedralSeparator.NormalizedCardMap f
      (OctahedralSeparator.fullImages ⟨i.val/6,by omega⟩ ⟨i.val%6,by omega⟩) h := by
  obtain ⟨i,hi⟩ := (marked_full_rank_iff f (actualMap h) hn).mp hr
  refine ⟨i,?_⟩
  intro k
  change actualMap h (complexMatrix (OctahedralSeparator.theta f (OctahedralSeparator.q k))) = _
  rw [hi,physicalMap_basis,sourceImages_high,OctahedralSeparator.complexTensor_action]
  rfl

end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
