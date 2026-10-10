import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover0Block (j : Fin 64) : Fin 722 := ⟨0+j.val,by omega⟩

def icosahedralCover0Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover0Block j))

theorem icosahedralCover0_checked : icosahedralCover0Audit=true := by decide +kernel

theorem icosahedralCover0_entry (i : Fin 722) (hlo : 0 ≤ i.val) (hhi : i.val < 64) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-0,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover0_checked j (by simp))
  have he : icosahedralCover0Block j=i := by apply Fin.ext; dsimp [icosahedralCover0Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
