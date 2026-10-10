import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover10Block (j : Fin 64) : Fin 722 := ⟨640+j.val,by omega⟩

def icosahedralCover10Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover10Block j))

theorem icosahedralCover10_checked : icosahedralCover10Audit=true := by decide +kernel

theorem icosahedralCover10_entry (i : Fin 722) (hlo : 640 ≤ i.val) (hhi : i.val < 704) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-640,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover10_checked j (by simp))
  have he : icosahedralCover10Block j=i := by apply Fin.ext; dsimp [icosahedralCover10Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
