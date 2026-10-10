import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows0Block (j : Fin 16) : Fin 272 := ⟨0+j.val,by omega⟩

def icosahedralRows0Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows0Block j))

theorem icosahedralRows0_checked : icosahedralRows0Audit=true := by decide +kernel

theorem icosahedralRows0_entry (i : Fin 272) (hlo : 0 ≤ i.val) (hhi : i.val < 16) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-0,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows0_checked j (by simp))
  have he : icosahedralRows0Block j=i := by apply Fin.ext; dsimp [icosahedralRows0Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
