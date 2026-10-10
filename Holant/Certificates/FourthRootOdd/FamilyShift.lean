import Holant.Certificates.FourthRootOdd.FamilyData
import Holant.Certificates.FourthRootOdd.PhaseWitness

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops Holant.Tractable

theorem phaseAt_shift (s : State) (δ : Fin 4) (x : Fin 4 → Bool) :
    phaseAt (shiftState s δ) 0 x=phaseAt s δ x := by
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> cases h₃ : x 3 <;>
    simp [phaseAt,alpha_shift,beta_shift,phaseCode_add,h₀,h₁,h₂,h₃]

theorem chartPhase_shift (s : State) (δ : Fin 4) : chartPhase (shiftState s δ) 0=chartPhase s δ := by
  funext y
  exact phaseAt_shift s δ (oddChart y)

theorem phaseTest_shift (s : State) (δ : Fin 4) : phaseTest (shiftState s δ) 0 ↔ phaseTest s δ := by
  unfold phaseTest
  rw [chartPhase_shift]

theorem shiftedOdd_shift (s : State) (δ : Fin 4) : shiftedOdd (shiftState s δ) 0=shiftedOdd s δ := by
  funext x
  simp [shiftedOdd,phaseAt_shift]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
theorem family_phase_test : ∀ p : FamilyParameters, phaseTest (familyState p) 0 := by decide

theorem family_affine (p : FamilyParameters) : Affine (shiftedOdd (familyState p) 0) :=
  shiftedOdd_affine _ _ (family_phase_test p)

end Holant.Certificates.FourthRootOdd
