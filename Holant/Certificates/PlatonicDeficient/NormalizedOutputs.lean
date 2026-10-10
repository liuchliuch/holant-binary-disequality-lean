import Holant.Certificates.PlatonicDeficient.OutputSemantics
import Holant.Certificates.PlatonicBridgeInterface.Interface

/-! The accepted A.27 exhaustive classifications select the six deficient
reconstructions directly from source normalization and genuine rank < 4.
There is no finite-candidate coverage hypothesis. -/
namespace Holant.Certificates.PlatonicDeficient
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem half_a_eq_source :
    (1/2 : ℂ) • A = complexTensor (tensorScale (rat (1/2)) aTensor) := by
  funext x
  have hq := complexMatrix_q 0
  change (1/2 : ℂ) * (Q0 (x 0) (x 1) * Q0 (x 2) (x 3)) = _
  simp only [complexTensor,tensorScale,aTensor,p0,embed_mul]
  rw [show embed (rat (1/2)) = (1/2 : ℂ) by norm_num [rat,embed_coeff]]
  change _ = (1/2 : ℂ) * (complexMatrix (q 0) (x 0) (x 1) * complexMatrix (q 0) (x 2) (x 3))
  rw [hq]
  rfl

private theorem half_b_eq_source :
    (1/2 : ℂ) • B = complexTensor (tensorScale (rat (1/2)) bTensor) := by
  funext x
  have hq := complexMatrix_q 0
  change (1/2 : ℂ) * (Q0 (x 0) (x 2) * Q0 (x 1) (x 3)) = _
  simp only [complexTensor,tensorScale,bTensor,p1,embed_mul]
  rw [show embed (rat (1/2)) = (1/2 : ℂ) by norm_num [rat,embed_coeff]]
  change _ = (1/2 : ℂ) * (complexMatrix (q 0) (x 0) (x 2) * complexMatrix (q 0) (x 1) (x 3))
  rw [hq]
  rfl

theorem sourceImages_low (p : Fin 6) (k : Fin 4) :
    TetrahedralBridge.sourceImages (p.castAdd 6) k = complexTensor (deficientImages p k) := by
  fin_cases p <;> fin_cases k <;>
    first
    | exact PlatonicBridgeInterface.Octahedral.half_c_eq_source
    | exact half_a_eq_source
    | exact half_b_eq_source
    | exact (funext fun _ => embed_zero.symm)

theorem actualMap_injective : Function.Injective PlatonicBridgeInterface.Octahedral.actualMap := by
  intro h g he
  funext x
  let U : Binary := fun a b => if a = x 0 ∧ b = x 1 then 1 else 0
  have hv := congrArg (fun Φ : Binary →ₗ[ℂ] FourTensor => Φ U (fun j => x j.succ.succ)) he
  simp only [PlatonicBridgeInterface.Octahedral.actualMap_apply,Signature.contract,U] at hv
  have hx : Fin.cons (x 0) (Fin.cons (x 1) (fun j : Fin 4 => x j.succ.succ)) = x := by
    funext j
    fin_cases j <;> rfl
  simpa [ite_and,hx] using hv

theorem standard_low_actualMap (p : Fin 6) :
    TetrahedralBridge.sourceMap (p.castAdd 6) =
      PlatonicBridgeInterface.Octahedral.actualMap (ancestor p) := by
  apply TetrahedralBridge.map_ext_basis
  intro k
  rw [TetrahedralBridge.sourceMap_basis,sourceImages_low]
  change _ = Signature.contract (quaternionBasis k) (ancestor p)
  funext x
  have hx := congrFun (reconstructed_basis_cards p k).symm x
  simpa only [complexMatrix_q,Signature.contract,Matrix.of_apply] using hx

theorem physical_low_actualMap (f : Form) (p : Fin 6) :
    PlatonicBridgeInterface.Octahedral.physicalMap f (p.castAdd 24) =
      PlatonicBridgeInterface.Octahedral.actualMap (complexTensor (deficientAncestor f p)) := by
  apply PlatonicBridgeInterface.Octahedral.map_ext_theta f
  intro k
  have he : PlatonicBridgeInterface.Octahedral.thetaEquiv f (quaternionBasis k) =
      complexMatrix (theta f (q k)) := by
    rw [complexMatrix_theta,complexMatrix_q]
    rfl
  rw [he,PlatonicBridgeInterface.Octahedral.physicalMap_basis]
  have hs : PlatonicBridgeInterface.Octahedral.sourceImages (p.castAdd 24) k =
      TetrahedralBridge.sourceImages (p.castAdd 6) k := by
    rw [←PlatonicBridgeInterface.Octahedral.sourceMap_basis,
      PlatonicBridgeInterface.Octahedral.low_map_eq,TetrahedralBridge.sourceMap_basis]
  rw [hs,sourceImages_low]
  symm
  exact (reconstructed_normalized f (deficientImages p) k).trans
    (complexTensor_action _ _)

theorem tetrahedral_rank_deficient (Φ : Binary →ₗ[ℂ] FourTensor)
    (hn : TetrahedralBridge.Normalized Φ) (hr : TetrahedralBridge.mapRank Φ < 4) :
    ∃ p : Fin 6, Φ = PlatonicBridgeInterface.Octahedral.actualMap (ancestor p) ∧
      TetrahedralBridge.mapRank Φ = 2 := by
  have hm := (TetrahedralBridge.mem_normalizedMaps Φ).mpr hn
  rw [TetrahedralBridge.normalizedMaps_partition] at hm
  rcases Finset.mem_union.mp hm with h2 | h4
  · have htwo := TetrahedralBridge.rankTwoMaps_rank h2
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp h2
    exact ⟨p,hp.symm.trans (standard_low_actualMap p),htwo⟩
  · rw [TetrahedralBridge.rankFourMaps_rank h4] at hr
    omega

theorem icosahedral_rank_deficient (Φ : Binary →ₗ[ℂ] FourTensor)
    (hn : IcosahedralSeparator.Normalized Φ) (hr : IcosahedralSeparator.mapRank Φ < 4) :
    ∃ p : Fin 6, Φ = PlatonicBridgeInterface.Octahedral.actualMap (ancestor p) ∧
      IcosahedralSeparator.mapRank Φ = 2 := by
  have hm := (IcosahedralSeparator.mem_normalizedMaps Φ).mpr hn
  rw [IcosahedralSeparator.normalizedMaps_partition] at hm
  rcases Finset.mem_union.mp hm with h2 | h4
  · have htwo := IcosahedralSeparator.rankTwoMaps_rank h2
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp h2
    refine ⟨p,?_,htwo⟩
    rw [←hp,IcosahedralSeparator.low_map_eq,standard_low_actualMap]
  · rw [IcosahedralSeparator.rankFourMaps_rank h4] at hr
    omega

theorem octahedral_rank_deficient (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor)
    (hn : PlatonicBridgeInterface.Octahedral.SourceHypotheses f Φ)
    (hr : PlatonicBridgeInterface.Octahedral.mapRank Φ < 4) :
    ∃ p : Fin 6, Φ = PlatonicBridgeInterface.Octahedral.actualMap
      (complexTensor (deficientAncestor f p)) ∧
      PlatonicBridgeInterface.Octahedral.mapRank Φ = 2 := by
  have hm := (PlatonicBridgeInterface.Octahedral.mem_markedNormalizedMaps f Φ).mpr hn
  rw [PlatonicBridgeInterface.Octahedral.markedNormalizedMaps_partition] at hm
  rcases Finset.mem_union.mp hm with h2 | h4
  · have htwo := PlatonicBridgeInterface.Octahedral.markedRankTwoMaps_rank f h2
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp h2
    exact ⟨p,hp.symm.trans (physical_low_actualMap f p),htwo⟩
  · rw [PlatonicBridgeInterface.Octahedral.markedRankFourMaps_rank f h4] at hr
    omega

/-- A normalized standard-form ancestor yields a literal support-ten output,
with actual native realization and all three complex flattening ranks. -/
def StandardDeficientOutput (g : PlatonicModel) (h : Signature ℂ 6) : Prop :=
  ∃ p : Fin 6, h = ancestor p ∧
    output p = Signature.contract Q0
      (Tensor.reindex (TetrahedralDeck.portOrder 1).symm h) ∧
    Gadget.Realizes (standardResources g h) .disequality (output p) ∧
    (support (output p)).card = 10 ∧
    ∀ r : Fin 3, (flatten r (output p)).rank = 3

theorem standard_deficient_of_ancestor (g : PlatonicModel) (h : Signature ℂ 6)
    (p : Fin 6) (he : h = ancestor p) : StandardDeficientOutput g h := by
  subst h
  exact ⟨p,rfl,output_contract p,output_realizes g p,output_support_ten p,output_rank_three p⟩

theorem tetrahedral_deficient_output (h : Signature ℂ 6)
    (hn : TetrahedralBridge.Normalized (PlatonicBridgeInterface.Octahedral.actualMap h))
    (hr : TetrahedralBridge.mapRank (PlatonicBridgeInterface.Octahedral.actualMap h) < 4) :
    StandardDeficientOutput .tetrahedral h := by
  obtain ⟨p,hp,_⟩ := tetrahedral_rank_deficient _ hn hr
  exact standard_deficient_of_ancestor .tetrahedral h p (actualMap_injective hp)

theorem icosahedral_deficient_output (h : Signature ℂ 6)
    (hn : IcosahedralSeparator.Normalized (IcosahedralSeparator.actualMap h))
    (hr : IcosahedralSeparator.mapRank (IcosahedralSeparator.actualMap h) < 4) :
    StandardDeficientOutput .icosahedral h := by
  obtain ⟨p,hp,_⟩ := icosahedral_rank_deficient _ hn hr
  have hm : IcosahedralSeparator.actualMap h = PlatonicBridgeInterface.Octahedral.actualMap h := by
    ext U x
    rfl
  rw [hm] at hp
  exact standard_deficient_of_ancestor .icosahedral h p (actualMap_injective hp)

theorem standard_ancestor_eq (p : Fin 6) :
    complexTensor (deficientAncestor 0 p) = ancestor p := by
  have hL : sixLegs 0 = (fun _ => (Signature.equality : Kernel Scalar)) := by
    decide +kernel
  rw [deficientAncestor,hL,Signature.coordinateAction_equality]
  rfl

theorem octahedral_deficient_output (h : Signature ℂ 6)
    (hn : PlatonicBridgeInterface.Octahedral.SourceHypotheses 0
      (PlatonicBridgeInterface.Octahedral.actualMap h))
    (hr : PlatonicBridgeInterface.Octahedral.mapRank
      (PlatonicBridgeInterface.Octahedral.actualMap h) < 4) :
    StandardDeficientOutput .octahedral h := by
  obtain ⟨p,hp,_⟩ := octahedral_rank_deficient 0 _ hn hr
  rw [standard_ancestor_eq] at hp
  exact standard_deficient_of_ancestor .octahedral h p (actualMap_injective hp)

/-- In the source normalized O′ coordinates the arbitrary original tensor is
one of the six literal actual ancestors, so the preceding graph applies. -/
theorem prime_deficient_output (h : Signature ℂ 6)
    (hn : PlatonicBridgeInterface.Octahedral.SourceHypotheses 1
      (PlatonicBridgeInterface.Octahedral.actualMap h))
    (hr : PlatonicBridgeInterface.Octahedral.mapRank
      (PlatonicBridgeInterface.Octahedral.actualMap h) < 4) :
    ∃ p : Fin 6, h = primeAncestor p ∧
      Gadget.Realizes (markedResources 1 h) .disequality (primeOutput p) ∧
      ∀ r : Fin 3, (flatten r (primeOutput p)).rank = 3 := by
  obtain ⟨p,hp,_⟩ := octahedral_rank_deficient 1 _ hn hr
  have he : h = primeAncestor p := actualMap_injective hp
  refine ⟨p,he,?_,primeOutput_rank_three p⟩
  rw [he]
  exact primeOutput_realizes p

end
end Holant.Certificates.PlatonicDeficient
