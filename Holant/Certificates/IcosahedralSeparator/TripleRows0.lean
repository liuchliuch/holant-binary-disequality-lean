import Holant.Certificates.IcosahedralSeparator.FiniteData

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem goodTriple_first_0 : ∀ b c : Fin 18,
    GoodTriple ![0,b,c] ↔ ∃ k : Fin 36, ![0,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_1 : ∀ b c : Fin 18,
    GoodTriple ![1,b,c] ↔ ∃ k : Fin 36, ![1,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_2 : ∀ b c : Fin 18,
    GoodTriple ![2,b,c] ↔ ∃ k : Fin 36, ![2,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_3 : ∀ b c : Fin 18,
    GoodTriple ![3,b,c] ↔ ∃ k : Fin 36, ![3,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_4 : ∀ b c : Fin 18,
    GoodTriple ![4,b,c] ↔ ∃ k : Fin 36, ![4,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_5 : ∀ b c : Fin 18,
    GoodTriple ![5,b,c] ↔ ∃ k : Fin 36, ![5,b,c] = ordered k := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
