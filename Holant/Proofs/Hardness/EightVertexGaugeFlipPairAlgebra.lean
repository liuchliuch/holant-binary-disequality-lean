import Holant.Proofs.Hardness.EightVertexGaugeFlipPairNetwork
import Holant.Proofs.Dichotomy.Retained.StableDenseResidualGaugeCore

/-! The exact two-I flip changes the selected two weights to their inverses
and retains the nonzero factor a*u2*u3. Agreement of the original and flipped
port fourth powers forces the common anchor to be an eighth root. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeFlipPairAlgebra
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
variable {K : Type} [Field K]

def weights (u : Fin 4 → K) : Fin 4 → K := ![u 0,u 1,(u 2)⁻¹,(u 3)⁻¹]

theorem weights_nonzero (u : Fin 4 → K) (hu : ∀ i, u i ≠ 0) : ∀ i, weights u i ≠ 0 := by
  intro i
  fin_cases i <;> simp [weights,hu]

theorem value (a : K) (u : Fin 4 → K) (hu : ∀ i, u i ≠ 0) :
    EightVertexGaugeFlipPairNetwork.value (weighted a u) =
      weighted (a*u 2*u 3) (weights u) := by
  funext x
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp [EightVertexGaugeFlipPairNetwork.value,weighted,table,weights] <;>
    field_simp [hu 2,hu 3]

theorem network_value (a : K) (u : Fin 4 → K) (hu : ∀ i, u i ≠ 0) :
    (EightVertexGaugeFlipPairNetwork.network (weighted a u)).denote =
      weighted (a*u 2*u 3) (weights u) := by
  rw [EightVertexGaugeFlipPairNetwork.denote,value a u hu]

/-- Reciprocal and unchanged ports are compared in the SAME original scale. -/
theorem eighth_power (u : Fin 4 → K) (hu0 : u 0 ≠ 0)
    (original : ∀ i, u i ^ 4 = u 0 ^ 4)
    (flipped : ∀ i, weights u i ^ 4 = weights u 0 ^ 4) : u 0 ^ 8 = 1 := by
  have hi : (u 2 ^ 4)⁻¹ = u 0 ^ 4 := by
    simpa [weights,inv_pow] using flipped 2
  rw [original 2] at hi
  calc
    u 0 ^ 8 = u 0 ^ 4*u 0 ^ 4 := by ring
    _ = (u 0 ^ 4)⁻¹*u 0 ^ 4 := congrArg (fun z => z*u 0 ^ 4) hi.symm
    _ = 1 := inv_mul_cancel₀ (pow_ne_zero 4 hu0)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeFlipPairAlgebra
end
