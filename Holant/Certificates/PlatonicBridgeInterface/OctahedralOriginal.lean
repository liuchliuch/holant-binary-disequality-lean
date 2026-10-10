import Holant.Certificates.PlatonicBridgeInterface.OctahedralSourceData

/-! Physical coefficient maps coincide with the actual original six-port
ancestors, and their fixed first cards agree without a scale or gauge change. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem map_ext_theta (f : Form) {Φ Ψ : Binary →ₗ[ℂ] FourTensor}
    (h : ∀ k : Fin 4, Φ (thetaEquiv f (quaternionBasis k)) =
      Ψ (thetaEquiv f (quaternionBasis k))) : Φ = Ψ := by
  have hu : unmarkMap f Φ = unmarkMap f Ψ := by
    apply TetrahedralBridge.map_ext_basis
    intro k
    change (coefficientEquiv f).symm (Φ (thetaEquiv f (quaternionBasis k))) = _
    rw [h k]
    rfl
  rw [←mark_unmark f Φ,hu,mark_unmark]

theorem physicalMap_full_ancestor (f : Form) (i : Fin 24) :
    physicalMap f (i.natAdd 6) = actualMap (OctahedralSeparator.complexTensor
      (OctahedralSeparator.fullAncestor f ⟨i.val/6,by omega⟩ ⟨i.val%6,by omega⟩)) := by
  apply map_ext_theta f
  intro k
  have he : thetaEquiv f (quaternionBasis k) = OctahedralSeparator.complexMatrix
      (OctahedralSeparator.theta f (OctahedralSeparator.q k)) := by
    rw [OctahedralSeparator.complexMatrix_theta,OctahedralSeparator.complexMatrix_q]
    rfl
  rw [he,physicalMap_basis,sourceImages_high]
  symm
  exact (OctahedralSeparator.reconstructed_normalized f _ k).trans
    (OctahedralSeparator.complexTensor_action _ _)

theorem actual_fixed_first_card (f : Form) (h : Signature ℂ 6)
    (hn : SourceHypotheses f (actualMap h)) (hr : mapRank (actualMap h) = 4) :
    ∃ i : Fin 24, Signature.contract
      (OctahedralSeparator.complexMatrix (OctahedralSeparator.theta f OctahedralSeparator.firstKernel)) h =
      OctahedralSeparator.complexTensor
        (OctahedralSeparator.coefficientCard f ((ordering i 0).castAdd 6)) := by
  obtain ⟨i,hi⟩ := actual_full_card_map f h hn hr
  exact ⟨i,OctahedralSeparator.normalized_first_card f _ _ h hi⟩

end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
