import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def tetrahedralCover0Block (j : Fin 34) : Fin 34 := ⟨0+j.val,by omega⟩

def tetrahedralCover0Audit : Bool := (List.finRange 34).all fun j => decide (RichCoverage .tetrahedral (tetrahedralCover0Block j))

theorem tetrahedralCover0_checked : tetrahedralCover0Audit=true := by decide +kernel

theorem tetrahedralCover0_entry (i : Fin 34) (hlo : 0 ≤ i.val) (hhi : i.val < 34) : RichCoverage .tetrahedral i := by
  let j : Fin 34 := ⟨i.val-0,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp tetrahedralCover0_checked j (by simp))
  have he : tetrahedralCover0Block j=i := by apply Fin.ext; dsimp [tetrahedralCover0Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
