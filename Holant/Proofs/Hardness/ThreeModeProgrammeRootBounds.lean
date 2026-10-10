import Holant.Proofs.Hardness.ThreeModeProgrammeRoots
import Holant.OneHot.ArithmeticSize

/-! Additive sum-product budgets for every actually generated root. The
original occurrence count, rather than the much longer root list, bounds each
root's multiplication degree. No repeated-squaring height assumption is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeProgrammeRootBounds
open Holant.OneHot
namespace A
export ThreeModeAnnihilator (mode rootIndices mem_rootIndices)
end A
namespace R
export ThreeModeProgrammeRoots (roots)
end R
variable {K I : Type} [Field K] (base : I→K)

/-- Exact degree budget for the repeated multiplication power programme. -/
theorem power_bound {u : K} (hu : ArithmeticSize.Bound base 1 u) (n : ℕ) :
    ArithmeticSize.Bound base n (u^n) := by
  induction n with
  | zero => simpa using (ArithmeticSize.Bound.one (coeff:=base))
  | succ n ih => simpa only [pow_succ] using ih.mul hu

variable {lam mu nu : K}
variable (hlam : ArithmeticSize.Bound base 1 lam)
variable (hmu : ArithmeticSize.Bound base 1 mu)
variable (hnu : ArithmeticSize.Bound base 1 nu)

include hlam hmu hnu in
theorem mode_bound (m i j : ℕ) (hij : i+j≤m) :
    ArithmeticSize.Bound base m (A.mode m lam mu nu (i,j)) := by
  have h := ((power_bound base hlam (m-i-j)).mul (power_bound base hmu i)).mul
    (power_bound base hnu j)
  have he : m-i-j+i+j=m := by omega
  simpa only [A.mode,he] using h

include hlam hmu hnu in
theorem roots_bound (m : ℕ) :
    ∀r∈R.roots lam mu nu m,ArithmeticSize.Bound base m r := by
  intro r hr
  obtain ⟨⟨i,j⟩,hij,rfl⟩ := List.mem_map.mp hr
  exact mode_bound base hlam hmu hnu m i j (A.mem_rootIndices.mp hij).1

include hlam in
theorem desired_bound (m : ℕ) : ArithmeticSize.Bound base m (lam^m) :=
  power_bound base hlam m

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeProgrammeRootBounds
