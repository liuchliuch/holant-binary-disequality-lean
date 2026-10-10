import Holant.Certificates.IcosahedralSeparator.FiniteData

namespace Holant.Certificates.IcosahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem goodTriple_first_12 : ∀ b c : Fin 18,
    GoodTriple ![12,b,c] ↔ ∃ k : Fin 36, ![12,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_13 : ∀ b c : Fin 18,
    GoodTriple ![13,b,c] ↔ ∃ k : Fin 36, ![13,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_14 : ∀ b c : Fin 18,
    GoodTriple ![14,b,c] ↔ ∃ k : Fin 36, ![14,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_15 : ∀ b c : Fin 18,
    GoodTriple ![15,b,c] ↔ ∃ k : Fin 36, ![15,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_16 : ∀ b c : Fin 18,
    GoodTriple ![16,b,c] ↔ ∃ k : Fin 36, ![16,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_17 : ∀ b c : Fin 18,
    GoodTriple ![17,b,c] ↔ ∃ k : Fin 36, ![17,b,c] = ordered k := by decide +kernel

end Holant.Certificates.IcosahedralSeparator
