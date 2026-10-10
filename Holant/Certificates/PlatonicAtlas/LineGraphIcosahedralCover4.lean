import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover4Block (j : Fin 64) : Fin 722 := ⟨256+j.val,by omega⟩

def icosahedralCover4Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover4Block j))

theorem icosahedralCover4_checked : icosahedralCover4Audit=true := by decide +kernel

theorem icosahedralCover4_entry (i : Fin 722) (hlo : 256 ≤ i.val) (hhi : i.val < 320) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-256,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover4_checked j (by simp))
  have he : icosahedralCover4Block j=i := by apply Fin.ext; dsimp [icosahedralCover4Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
