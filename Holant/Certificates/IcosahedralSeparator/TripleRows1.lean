import Holant.Certificates.IcosahedralSeparator.FiniteData

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem goodTriple_first_6 : ∀ b c : Fin 18,
    GoodTriple ![6,b,c] ↔ ∃ k : Fin 36, ![6,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_7 : ∀ b c : Fin 18,
    GoodTriple ![7,b,c] ↔ ∃ k : Fin 36, ![7,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_8 : ∀ b c : Fin 18,
    GoodTriple ![8,b,c] ↔ ∃ k : Fin 36, ![8,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_9 : ∀ b c : Fin 18,
    GoodTriple ![9,b,c] ↔ ∃ k : Fin 36, ![9,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_10 : ∀ b c : Fin 18,
    GoodTriple ![10,b,c] ↔ ∃ k : Fin 36, ![10,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_11 : ∀ b c : Fin 18,
    GoodTriple ![11,b,c] ↔ ∃ k : Fin 36, ![11,b,c] = ordered k := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
