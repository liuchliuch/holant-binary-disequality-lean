import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover6Block (j : Fin 64) : Fin 722 := ⟨384+j.val,by omega⟩

def icosahedralCover6Audit : Bool := (List.finRange 64).all fun j => decide (RichCoverage .icosahedral (icosahedralCover6Block j))

theorem icosahedralCover6_checked : icosahedralCover6Audit=true := by decide +kernel

theorem icosahedralCover6_entry (i : Fin 722) (hlo : 384 ≤ i.val) (hhi : i.val < 448) : RichCoverage .icosahedral i := by
  let j : Fin 64 := ⟨i.val-384,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover6_checked j (by simp))
  have he : icosahedralCover6Block j=i := by apply Fin.ext; dsimp [icosahedralCover6Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
