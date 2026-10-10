import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def octahedralRows2Block (j : Fin 16) : Fin 50 := ⟨32+j.val,by omega⟩

def octahedralRows2Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .octahedral (octahedralRows2Block j))

theorem octahedralRows2_checked : octahedralRows2Audit=true := by decide +kernel

theorem octahedralRows2_entry (i : Fin 50) (hlo : 32 ≤ i.val) (hhi : i.val < 48) : RichEntry .octahedral i := by
  let j : Fin 16 := ⟨i.val-32,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp octahedralRows2_checked j (by simp))
  have he : octahedralRows2Block j=i := by apply Fin.ext; dsimp [octahedralRows2Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
