import Holant.Proofs.Hardness.GeneralCancellationCapPin
import Holant.Proofs.Dichotomy.Retained.StableDenseResidualGaugeCore

/-! All six original native-X loops on a weighted-even row. The scalar is
a*(ui+uj) and the remaining two port weights are retained. With nonzero port
weights these one-row loops vanish at both entries or at neither entry, so
none of them alone supplies the single-pin resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeCaps
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
namespace Cap
export GeneralCancellationCapPin (Choice oriented coefficients antiTensor network full_table)
end Cap
variable {K : Type} [Field K]

def loopPorts (c : Fin 6) : Fin 4 × Fin 4 :=
  ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)] c

def remainingPorts (c : Fin 6) : Fin 4 × Fin 4 :=
  ![(2,3),(1,3),(1,2),(0,3),(0,2),(0,1)] c

def scalar (a : K) (u : Fin 4 → K) (c : Fin 6) : K :=
  a*(u (loopPorts c).1+u (loopPorts c).2)

theorem weighted_even (a : K) (u : Fin 4 → K) : EvenSupport (weighted a u) := by
  intro x hx
  rw [weighted_value]
  simp [hx]

theorem coefficients (a : K) (u : Fin 4 → K) (c : Fin 6) :
    Cap.coefficients (weighted a u) c =
      (scalar a u c*u (remainingPorts c).2,scalar a u c*u (remainingPorts c).1) := by
  fin_cases c <;>
    simp [Cap.coefficients,GeneralCancellationCapPin.coefficients,weighted,entries,table,
      scalar,loopPorts,remainingPorts] <;> constructor <;> ring

theorem exact_cap (a : K) (u : Fin 4 → K) (c : Fin 6) (rev : Bool) :
    (Cap.network (weighted a u) (c,rev)).denote =
      fun x => scalar a u c * Cap.antiTensor
        (u (if rev then (remainingPorts c).1 else (remainingPorts c).2))
        (u (if rev then (remainingPorts c).2 else (remainingPorts c).1)) x := by
  rw [Cap.full_table _ (weighted_even a u)]
  funext x
  cases rev <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Cap.oriented,GeneralCancellationCapPin.oriented,coefficients,
      Cap.antiTensor,GeneralCancellationCapPin.antiTensor,h0,h1]

/-- These physical caps cannot distinguish the two surviving orientations
by zero/nonzero when every original port weight is nonzero. -/
theorem oriented_zero_iff (a : K) (u : Fin 4 → K) (hu : ∀ i, u i ≠ 0)
    (k : Cap.Choice) :
    (Cap.oriented (weighted a u) k).1 = 0 ↔
      (Cap.oriented (weighted a u) k).2 = 0 := by
  rcases k with ⟨c,rev⟩
  cases rev <;>
    simp [Cap.oriented,GeneralCancellationCapPin.oriented,coefficients,hu]

theorem no_single_pin (a : K) (u : Fin 4 → K) (hu : ∀ i, u i ≠ 0) :
    ¬ GeneralCancellationCapPin.Applicable (weighted a u) := by
  rintro ⟨k,live,zero⟩
  exact live ((oriented_zero_iff a u hu k).mpr zero)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeCaps
end
