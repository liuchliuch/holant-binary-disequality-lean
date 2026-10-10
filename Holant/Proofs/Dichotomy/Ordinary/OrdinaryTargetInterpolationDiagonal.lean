import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationPhysical

/-! Exact diagonal spectral pencil for ordinary chain interpolation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationDiagonal
open Holant Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
variable {K : Type} [Field K]
def diagonal (a b : K) : Binary (K:=K) := fun x y=>if x=y then (if x then b else a) else 0

theorem mul (a b c d : K) : diagonal a b * diagonal c d=diagonal (a*c) (b*d) := by
  ext x y
  cases x <;> cases y <;> simp [diagonal,Matrix.mul_apply,Fintype.sum_bool]

theorem power (a b : K) (k : ℕ) : (diagonal a b)^k=diagonal (a^k) (b^k) := by
  induction k with
  | zero => ext x y; cases x <;> cases y <;> simp [diagonal]
  | succ k ih => rw [pow_succ,ih,mul,pow_succ,pow_succ]

theorem pencil (a b : K) (ha : a≠0) (k : ℕ) :
    (diagonal a b)^k=a^k • (diagonal 1 0+(b/a)^k • diagonal 0 1) := by
  rw [power]
  ext x y
  cases x <;> cases y <;> simp [diagonal,div_pow]
  field_simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryTargetInterpolationDiagonal
end
