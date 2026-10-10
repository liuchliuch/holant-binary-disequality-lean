import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def octahedralCover1Block (j : Fin 58) : Fin 122 := ⟨64+j.val,by omega⟩

def octahedralCover1Audit : Bool := (List.finRange 58).all fun j => decide (RichCoverage .octahedral (octahedralCover1Block j))

theorem octahedralCover1_checked : octahedralCover1Audit=true := by decide +kernel

theorem octahedralCover1_entry (i : Fin 122) (hlo : 64 ≤ i.val) (hhi : i.val < 122) : RichCoverage .octahedral i := by
  let j : Fin 58 := ⟨i.val-64,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp octahedralCover1_checked j (by simp))
  have he : octahedralCover1Block j=i := by apply Fin.ext; dsimp [octahedralCover1Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
