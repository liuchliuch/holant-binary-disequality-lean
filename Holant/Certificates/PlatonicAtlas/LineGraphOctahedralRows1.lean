import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def octahedralRows1Block (j : Fin 16) : Fin 50 := ⟨16+j.val,by omega⟩

def octahedralRows1Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .octahedral (octahedralRows1Block j))

theorem octahedralRows1_checked : octahedralRows1Audit=true := by decide +kernel

theorem octahedralRows1_entry (i : Fin 50) (hlo : 16 ≤ i.val) (hhi : i.val < 32) : RichEntry .octahedral i := by
  let j : Fin 16 := ⟨i.val-16,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp octahedralRows1_checked j (by simp))
  have he : octahedralRows1Block j=i := by apply Fin.ext; dsimp [octahedralRows1Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
