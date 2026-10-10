import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows10Block (j : Fin 16) : Fin 272 := ⟨160+j.val,by omega⟩

def icosahedralRows10Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows10Block j))

theorem icosahedralRows10_checked : icosahedralRows10Audit=true := by decide +kernel

theorem icosahedralRows10_entry (i : Fin 272) (hlo : 160 ≤ i.val) (hhi : i.val < 176) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-160,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows10_checked j (by simp))
  have he : icosahedralRows10Block j=i := by apply Fin.ext; dsimp [icosahedralRows10Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
