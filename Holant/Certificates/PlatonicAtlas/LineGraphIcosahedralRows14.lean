import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows14Block (j : Fin 16) : Fin 272 := ⟨224+j.val,by omega⟩

def icosahedralRows14Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows14Block j))

theorem icosahedralRows14_checked : icosahedralRows14Audit=true := by decide +kernel

theorem icosahedralRows14_entry (i : Fin 272) (hlo : 224 ≤ i.val) (hhi : i.val < 240) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-224,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows14_checked j (by simp))
  have he : icosahedralRows14Block j=i := by apply Fin.ext; dsimp [icosahedralRows14Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
