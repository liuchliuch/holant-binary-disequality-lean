import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def octahedralRows3Block (j : Fin 2) : Fin 50 := ⟨48+j.val,by omega⟩

def octahedralRows3Audit : Bool := (List.finRange 2).all fun j => decide (RichEntry .octahedral (octahedralRows3Block j))

theorem octahedralRows3_checked : octahedralRows3Audit=true := by decide +kernel

theorem octahedralRows3_entry (i : Fin 50) (hlo : 48 ≤ i.val) (hhi : i.val < 50) : RichEntry .octahedral i := by
  let j : Fin 2 := ⟨i.val-48,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp octahedralRows3_checked j (by simp))
  have he : octahedralRows3Block j=i := by apply Fin.ext; dsimp [octahedralRows3Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
