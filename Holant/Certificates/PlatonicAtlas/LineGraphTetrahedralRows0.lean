import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def tetrahedralRows0Block (j : Fin 16) : Fin 16 := ⟨0+j.val,by omega⟩

def tetrahedralRows0Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .tetrahedral (tetrahedralRows0Block j))

theorem tetrahedralRows0_checked : tetrahedralRows0Audit=true := by decide +kernel

theorem tetrahedralRows0_entry (i : Fin 16) (hlo : 0 ≤ i.val) (hhi : i.val < 16) : RichEntry .tetrahedral i := by
  let j : Fin 16 := ⟨i.val-0,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp tetrahedralRows0_checked j (by simp))
  have he : tetrahedralRows0Block j=i := by apply Fin.ext; dsimp [tetrahedralRows0Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
