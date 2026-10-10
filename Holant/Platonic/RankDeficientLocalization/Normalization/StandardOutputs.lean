import Holant.Platonic.RankDeficientLocalization.Normalization.PhysicalAssembly

/-! The arbitrary unnormalized standard T/O/I input yields one of the six
literal A.24 outputs by an ordinary graph with one original six-port vertex. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical

abbrev actualMap := PlatonicBridgeInterface.Octahedral.actualMap

theorem sourceEquations_deficient (g : PlatonicModel) (Φ : Mat →ₗ[ℂ] FourTensor)
    (hn : SourceEquations g Φ) (hr : Module.finrank ℂ Φ.range<4) :
    ∃p : Fin 6, Φ=actualMap (PlatonicDeficient.ancestor p) ∧ Module.finrank ℂ Φ.range=2 := by
  have hRank : PlatonicBridgeInterface.Octahedral.mapRank Φ=Module.finrank ℂ Φ.range :=
    PlatonicBridgeInterface.Octahedral.mapRank_eq_finrank Φ
  cases g
  · obtain ⟨p,hp,hrank⟩ := PlatonicDeficient.tetrahedral_rank_deficient Φ
      ((TetrahedralBridge.normalized_iff_source Φ).mpr hn) (by change PlatonicBridgeInterface.Octahedral.mapRank Φ<4; omega)
    exact ⟨p,hp,by change PlatonicBridgeInterface.Octahedral.mapRank Φ=2 at hrank; omega⟩
  · have hnorm := (PlatonicBridgeInterface.Octahedral.normalized_iff_source Φ).mpr hn
    have hm := (PlatonicBridgeInterface.Octahedral.mem_normalizedMaps Φ).mpr hnorm
    rw [PlatonicBridgeInterface.Octahedral.normalizedMaps_partition] at hm
    rcases Finset.mem_union.mp hm with h2|h4
    · have hrank := PlatonicBridgeInterface.Octahedral.rankTwoMaps_rank h2
      obtain ⟨p,_,hp⟩ := Finset.mem_image.mp h2
      refine ⟨p,?_,by omega⟩
      rw [←hp,PlatonicBridgeInterface.Octahedral.low_map_eq,PlatonicDeficient.standard_low_actualMap]
    · have hfour := PlatonicBridgeInterface.Octahedral.rankFourMaps_rank h4
      omega
  · obtain ⟨p,hp,hrank⟩ := PlatonicDeficient.icosahedral_rank_deficient Φ
      ((IcosahedralSeparator.normalized_iff_source Φ).mpr hn) (by change PlatonicBridgeInterface.Octahedral.mapRank Φ<4; omega)
    exact ⟨p,hp,by change PlatonicBridgeInterface.Octahedral.mapRank Φ=2 at hrank; omega⟩

/-- The rank-three possibility is excluded only after the full actual
normalization and the exhaustive bridge classification have been proved. -/
theorem standard_deficient_normalization (g : PlatonicModel) (h : Signature ℂ 6)
    (hc : ∀i,matchingCone g (actualMap h (representative g i)))
    (hm : MixedCards (actualMap h) (representative g))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,∃D : DomainAction g,∃L : Legs,GroupLegs g L ∧
      (SixDressing.ofDomain D L).tensor h=PlatonicDeficient.ancestor p ∧
      Module.finrank ℂ (actualMap h).range=2 := by
  obtain ⟨R⟩ := platonic_mixed_rainbow g (LinearEquiv.refl ℂ Mat) (actualMap h)
    (fun i => matchingCone_card g _ (hc i)) hm
  obtain ⟨D,L,hL,hn,hrank⟩ := source_normalization (actualMap h) R hc
  obtain ⟨p,hp,h2⟩ := sourceEquations_deficient g (dressedMap D L (actualMap h)) hn (by omega)
  refine ⟨p,D,L,hL,?_,by omega⟩
  apply PlatonicDeficient.actualMap_injective
  rw [ofDomain_actualMap]
  exact hp

/-- A.24's standard-form contraction: no caller normalization, finite-table
coverage, card colours, or chosen rich line occurs in the hypotheses. -/
theorem standard_deficient_output (g : PlatonicModel) (h : Signature ℂ 6)
    (hc : ∀i,matchingCone g (actualMap h (representative g i)))
    (hm : MixedCards (actualMap h) (representative g))
    (hr : Module.finrank ℂ (actualMap h).range<4) :
    ∃p : Fin 6,∃D : SixDressing,
      Module.finrank ℂ (actualMap h).range=2 ∧
      (D.network h).denote=PlatonicDeficient.output p ∧
      (∀v,(⟨(D.network h).shape.arity v,(D.network h).vertex v⟩ : AnySignature ℂ) ∈
        PlatonicDeficient.standardResources g h) ∧
      (∀e,(D.network h).edge e=Signature.disequality) ∧
      (D.network h).vertex (0 : Fin 6)=h ∧
      (D.network h).shape.vertices=6 ∧ (D.network h).shape.edges=6 ∧
      (PlatonicDeficient.support (PlatonicDeficient.output p)).card=10 ∧
      ∀r : Fin 3,(flatten r (PlatonicDeficient.output p)).rank=3 := by
  obtain ⟨p,D,L,hL,he,h2⟩ := standard_deficient_normalization g h hc hm hr
  let N := SixDressing.ofDomain D L
  refine ⟨p,N,h2,?_,N.network_resources g (ofDomain_legs_mem D L hL) h,
    (fun _ => rfl),N.network_ancestor h,rfl,rfl,PlatonicDeficient.output_support_ten p,
    PlatonicDeficient.output_rank_three p⟩
  rw [SixDressing.network_denote,he,PlatonicDeficient.output_contract]

end
end Holant.Platonic.RankDeficientLocalization.Normalization
