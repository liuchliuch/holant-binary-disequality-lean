import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover7Block (j : Fin 64) : Fin 722 := ⟨448+j.val,by omega⟩

def icosahedralCover7Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover7Block j))

theorem icosahedralCover7_checked : icosahedralCover7Audit=true := by decide +kernel

theorem icosahedralCover7_entry (i : Fin 722) (hlo : 448 ≤ i.val) (hhi : i.val < 512) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-448,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover7_checked j (by simp))
  have he : icosahedralCover7Block j=i := by apply Fin.ext; dsimp [icosahedralCover7Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
