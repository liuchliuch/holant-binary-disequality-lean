import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover1Block (j : Fin 64) : Fin 722 := ⟨64+j.val,by omega⟩

def icosahedralCover1Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover1Block j))

theorem icosahedralCover1_checked : icosahedralCover1Audit=true := by decide +kernel

theorem icosahedralCover1_entry (i : Fin 722) (hlo : 64 ≤ i.val) (hhi : i.val < 128) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-64,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover1_checked j (by simp))
  have he : icosahedralCover1Block j=i := by apply Fin.ext; dsimp [icosahedralCover1Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
