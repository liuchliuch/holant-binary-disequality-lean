import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationDiagonal
import Holant.Complexity.BinaryInterpolation.Chains.RecordCorrespondence

/-! Exact native-X antidiagonal chain pencil. No identity vertex is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetAlgebra
open Holant Holant.Certificates.MatchingContractionClosure
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal power pencil)
end D
set_option maxHeartbeats 200000
set_option Elab.async false
variable {K : Type} [Field K]
def anti (p q : K) : Binary (K:=K):=fun x y=>if x=y then 0 else if x then q else p

theorem transfer (p q : K) : anti p q*X=D.diagonal p q := by
  ext x y
  cases x <;> cases y <;> simp [anti,X,D.diagonal,Matrix.mul_apply,Signature.disequality]

theorem diagonal_x (p q : K) : D.diagonal p q*X=anti p q := by
  ext x y
  cases x <;> cases y <;> simp [anti,X,D.diagonal,Matrix.mul_apply,Signature.disequality]

theorem powers (p q : K) (k : ℕ) : (anti p q*X)^k*X=anti (p^k) (q^k) := by
  rw [transfer,D.power,diagonal_x]

theorem pencil (p q : K) (hp : p≠0) (k : ℕ) :
    (anti p q*X)^k*X=p^k • (anti 1 0+(q/p)^k • anti 0 1) := by
  rw [powers]
  ext x y
  cases x <;> cases y <;> simp [anti,div_pow]
  field_simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetAlgebra
end
