import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover3Block (j : Fin 64) : Fin 722 := ⟨192+j.val,by omega⟩

def icosahedralCover3Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover3Block j))

theorem icosahedralCover3_checked : icosahedralCover3Audit=true := by decide +kernel

theorem icosahedralCover3_entry (i : Fin 722) (hlo : 192 ≤ i.val) (hhi : i.val < 256) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-192,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover3_checked j (by simp))
  have he : icosahedralCover3Block j=i := by apply Fin.ext; dsimp [icosahedralCover3Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
