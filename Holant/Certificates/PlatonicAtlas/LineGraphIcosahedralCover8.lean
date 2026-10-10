import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover8Block (j : Fin 64) : Fin 722 := ⟨512+j.val,by omega⟩

def icosahedralCover8Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover8Block j))

theorem icosahedralCover8_checked : icosahedralCover8Audit=true := by decide +kernel

theorem icosahedralCover8_entry (i : Fin 722) (hlo : 512 ≤ i.val) (hhi : i.val < 576) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-512,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover8_checked j (by simp))
  have he : icosahedralCover8Block j=i := by apply Fin.ext; dsimp [icosahedralCover8Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
