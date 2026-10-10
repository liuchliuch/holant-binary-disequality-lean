import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCases
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesTarget

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesTrace
open Holant
namespace P
export GlobalCloseCompletionPairedSeriesCore (row series series_denote power power_denote identity smul)
end P
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal)
end D
namespace R
export GlobalCloseCompletionPairedSeriesRelabel (correct correct_value relabel)
end R
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K]
theorem square (B : Matrix Bool Bool K) (same : B true true=B false false) :
    (B*D.diagonal 1 (-1))^2=B.det • (1 : Matrix Bool Bool K) := by
  ext i j
  cases i <;> cases j <;>
    simp [pow_two,Matrix.mul_apply,D.diagonal,Holant.Complexity.BinaryInterpolation.det_entries,
      Matrix.one_apply,same] <;> ring

variable {s : ℕ} {a : ℕ→ℕ} {H : (i : Fin s)→Signature K (a i.val)}
theorem power_eq4 (N : M.Macro H 4) (B : Matrix Bool Bool K) (hN : N.network.denote=P.row B)
    (k : ℕ) (hk : 0<k) (c : K) (power : B^k=c • (1 : Matrix Bool Bool K)) :
    (P.power N (k-1)).network.denote=c • Holant.EightVertex.ProductAnchor.equalityFour := by
  rw [P.power_denote N B hN,Nat.sub_add_cancel hk,power,P.smul,P.identity]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesTrace
end
