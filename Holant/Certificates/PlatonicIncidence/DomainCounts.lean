import Holant.Certificates.PlatonicIncidence.Subspaces

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Exact numbers of actual secants by size, including the ordinary two-point
lines needed to cover arbitrary complex-subspace deletions. -/
theorem tetrahedral_domain_counts :
    ((domainLines .tetrahedral).filter (fun S => S.card=2)).card=18 ∧
    ((domainLines .tetrahedral).filter (fun S => S.card=3)).card=16 ∧
    ((domainLines .tetrahedral).filter (fun S => S.card=4)).card=0 ∧
    ((domainLines .tetrahedral).filter (fun S => S.card=5)).card=0 := by
  simp only [domainLines_filter_card]
  exact tetrahedral_size_distribution

theorem octahedral_domain_counts :
    ((domainLines .octahedral).filter (fun S => S.card=2)).card=72 ∧
    ((domainLines .octahedral).filter (fun S => S.card=3)).card=32 ∧
    ((domainLines .octahedral).filter (fun S => S.card=4)).card=18 ∧
    ((domainLines .octahedral).filter (fun S => S.card=5)).card=0 := by
  simp only [domainLines_filter_card]
  exact octahedral_size_distribution

theorem icosahedral_domain_counts :
    ((domainLines .icosahedral).filter (fun S => S.card=2)).card=450 ∧
    ((domainLines .icosahedral).filter (fun S => S.card=3)).card=200 ∧
    ((domainLines .icosahedral).filter (fun S => S.card=4)).card=0 ∧
    ((domainLines .icosahedral).filter (fun S => S.card=5)).card=72 := by
  simp only [domainLines_filter_card]
  exact icosahedral_size_distribution

theorem domainLines_size_bound (g : PlatonicModel) (S : Finset (Fin (size g)))
    (hS : S∈domainLines g) : 2≤S.card ∧ S.card≤maximumLineSize g := by
  obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp hS
  exact globalLine_bound g t

end
end Holant.Certificates.PlatonicIncidence
