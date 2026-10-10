import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralCover11Block (j : Fin 18) : Fin 722 := ⟨704+j.val,by omega⟩

def icosahedralCover11Audit : Bool := (List.finRange 18).all fun j => decide (RichCoverage .icosahedral (icosahedralCover11Block j))

theorem icosahedralCover11_checked : icosahedralCover11Audit=true := by decide +kernel

theorem icosahedralCover11_entry (i : Fin 722) (hlo : 704 ≤ i.val) (hhi : i.val < 722) : RichCoverage .icosahedral i := by
  let j : Fin 18 := ⟨i.val-704,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralCover11_checked j (by simp))
  have he : icosahedralCover11Block j=i := by apply Fin.ext; dsimp [icosahedralCover11Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
