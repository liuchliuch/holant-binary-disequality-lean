import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def octahedralCover0Block (j : Fin 64) : Fin 122 := ⟨0+j.val,by omega⟩

def octahedralCover0Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .octahedral (octahedralCover0Block j))

theorem octahedralCover0_checked : octahedralCover0Audit=true := by decide +kernel

theorem octahedralCover0_entry (i : Fin 122) (hlo : 0 ≤ i.val) (hhi : i.val < 64) : RichCoverage .octahedral i := by
  let j : Fin 64 := ⟨i.val-0,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp octahedralCover0_checked j (by simp))
  have he : octahedralCover0Block j=i := by apply Fin.ext; dsimp [octahedralCover0Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
