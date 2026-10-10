import Holant.Certificates.PlatonicBridgeInterface.OctahedralMaps
import Holant.Certificates.OctahedralSeparator.BaseRanks
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixMinors

/-! Pure six-port O coefficient checks, without the historical saved-state
source chain. The24 full maps fail a literal Q0+Q1 contraction; the six
remaining maps share the already checked deficient T obstruction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralSixGeometry
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant.Certificates.OctahedralSeparator (complexTensor complexMatrix)
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


theorem low_map_eq (i : Fin 6) : sourceMap (i.castAdd 24)=TetrahedralBridge.sourceMap (i.castAdd 6) := by
  apply TetrahedralBridge.map_ext_basis
  intro k
  rw [sourceMap_basis,TetrahedralBridge.sourceMap_basis]
  fin_cases i <;> fin_cases k <;> rfl

theorem regularCard_not_matching (g : PlatonicModel) (j : Fin 9) :
    ¬matchingCone g (complexTensor (OctahedralSeparator.regularCard j)) := by
  intro h
  rcases matchingCone_presentation g _ h with zero | ⟨r,U,V,hU,hV,he⟩
  · have hr := OctahedralSeparator.base_rank_two j 0
    rw [zero] at hr
    have hz : flatten 0 (0 : FourTensor)=0 := rfl
    rw [hz,Matrix.rank_zero] at hr
    norm_num at hr
  · have hr := OctahedralSeparator.base_rank_two j r
    rw [he,matching_flattening_rank r r U V (groupDirection_det_ne_zero g hU) (groupDirection_det_ne_zero g hV),if_pos rfl] at hr
    omega

theorem full_first_card (i : Fin 24) :
    sourceMap (i.natAdd 6) (Q0+Q1)=complexTensor
      (OctahedralSeparator.regularCard
        (OctahedralSeparator.frames ⟨i.val/6,by omega⟩
          (OctahedralSeparator.permutations ⟨i.val%6,by omega⟩ 0))) := by
  have h0 := sourceMap_basis (i.natAdd 6) 0
  have h1 := sourceMap_basis (i.natAdd 6) 1
  change sourceMap (i.natAdd 6) Q0=_ at h0
  change sourceMap (i.natAdd 6) Q1=_ at h1
  rw [map_add,h0,h1,sourceImages_high,sourceImages_high]
  funext x
  change OctahedralSeparator.embed (_)+OctahedralSeparator.embed (_)=_
  rw [←OctahedralSeparator.embed_add]
  rfl

theorem firstKernel_mem : groupDirection .octahedral (Q0+Q1) := by
  refine ⟨1,one_ne_zero,Q0+Q1,?_,by simp only [one_smul]⟩
  change octahedralBase (Q0+Q1)
  refine Or.inr ⟨0,1,by decide,false,?_⟩
  norm_num [signBit,quaternionBasis]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralSixGeometry
end
