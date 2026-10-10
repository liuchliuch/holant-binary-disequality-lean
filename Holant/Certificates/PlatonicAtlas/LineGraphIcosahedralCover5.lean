import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover5Block (j : Fin 64) : Fin 722 := ⟨320+j.val,by omega⟩

def icosahedralCover5Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover5Block j))

theorem icosahedralCover5_checked : icosahedralCover5Audit=true := by decide +kernel

theorem icosahedralCover5_entry (i : Fin 722) (hlo : 320 ≤ i.val) (hhi : i.val < 384) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-320,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover5_checked j (by simp))
  have he : icosahedralCover5Block j=i := by apply Fin.ext; dsimp [icosahedralCover5Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
