import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover2Block (j : Fin 64) : Fin 722 := ⟨128+j.val,by omega⟩

def icosahedralCover2Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover2Block j))

theorem icosahedralCover2_checked : icosahedralCover2Audit=true := by decide +kernel

theorem icosahedralCover2_entry (i : Fin 722) (hlo : 128 ≤ i.val) (hhi : i.val < 192) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-128,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover2_checked j (by simp))
  have he : icosahedralCover2Block j=i := by apply Fin.ext; dsimp [icosahedralCover2Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
