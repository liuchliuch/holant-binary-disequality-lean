import Holant.Certificates.PlatonicBridgeInterface.OctahedralOriginal
import Holant.Certificates.OctahedralSeparator.PublicClauses

/-! Unrestricted actual-map input to the accepted current-form separator. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

theorem actual_full_rank_exits (f : Form) (h : Signature ℂ 6)
    (hn : SourceHypotheses f (actualMap h)) (hr : mapRank (actualMap h) = 4) :
    OctahedralSeparator.Resolved f h := by
  obtain ⟨i,hi⟩ := actual_full_card_map f h hn hr
  exact OctahedralSeparator.uniform_octahedral_full_rank_exits f _ _ h hi

theorem actual_unmixed_eight_vertex (f : Fin 2) (h : Signature ℂ 6)
    (hn : SourceHypotheses (f.castAdd 2) (actualMap h)) (hr : mapRank (actualMap h) = 4) :
    OctahedralSeparator.EndpointExit (f.castAdd 2) h := by
  obtain ⟨i,hi⟩ := actual_full_card_map (f.castAdd 2) h hn hr
  exact OctahedralSeparator.standard_prime_eight_vertex f _ _ h hi


end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
