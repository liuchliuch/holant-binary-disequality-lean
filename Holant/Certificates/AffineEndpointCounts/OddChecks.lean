import Holant.Certificates.AffineEndpointCounts.OddData

/-! Kernel-checked exact counts and shift sets on the injective 512-table family. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem odd_even_shift_parameter_count : (oddPhaseParameters 0).card=176 := by decide +kernel

theorem odd_odd_shift_parameter_count : (oddPhaseParameters 1).card=128 := by decide +kernel

theorem odd_family_phase_set : ∀ (p : FamilyParameters) (δ : Fin 4),
    phaseTest (oddFamilyPreimage 0 p) δ ↔ δ=0 ∨ δ=2 := by decide +kernel

theorem odd_shifted_family_phase_set : ∀ (p : FamilyParameters) (δ : Fin 4),
    phaseTest (oddFamilyPreimage 1 p) δ ↔ δ=1 ∨ δ=3 := by decide +kernel

end Holant.Certificates.AffineEndpointCounts
