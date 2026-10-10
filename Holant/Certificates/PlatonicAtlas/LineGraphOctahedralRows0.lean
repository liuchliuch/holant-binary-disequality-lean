import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def octahedralRows0Block (j : Fin 16) : Fin 50 := ⟨0+j.val,by omega⟩

def octahedralRows0Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .octahedral (octahedralRows0Block j))

theorem octahedralRows0_checked : octahedralRows0Audit=true := by decide +kernel

theorem octahedralRows0_entry (i : Fin 50) (hlo : 0 ≤ i.val) (hhi : i.val < 16) : RichEntry .octahedral i := by
  let j : Fin 16 := ⟨i.val-0,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp octahedralRows0_checked j (by simp))
  have he : octahedralRows0Block j=i := by apply Fin.ext; dsimp [octahedralRows0Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
