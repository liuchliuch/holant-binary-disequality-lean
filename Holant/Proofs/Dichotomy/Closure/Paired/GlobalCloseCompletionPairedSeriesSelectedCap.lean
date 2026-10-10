import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCases
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCaps

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesSelectedCap
open Holant Holant.Complexity Holant.Tractable
open Holant.Certificates.MatchingContractionClosure
namespace P
export GlobalCloseCompletionPairedSeriesCore (row power power_denote)
export GlobalCloseCompletionPairedSeriesCaps (transposePorts transpose_value rowCap rowCap_value)
end P
namespace C
export GlobalCloseCompletionPairedSeriesChoice (Cap Read Infinite)
end C
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (a i.val)}
def selected (N : M.Macro H 4) (k : ℕ) (swap : Bool) : M.Macro H 4 :=
  if swap then (P.power N (k-1)).reindex P.transposePorts else P.power N (k-1)
theorem selected_value (N : M.Macro H 4) (B : Matrix Bool Bool K)
    (hN : N.network.denote=P.row B) (k : ℕ) (hk : 0<k) (swap : Bool) :
    (selected N k swap).network.denote=P.row (C.Read B k swap) := by
  have hp : (P.power N (k-1)).network.denote=P.row (B^k) := by
    simpa only [Nat.sub_add_cancel hk] using P.power_denote N B hN (k-1)
  cases swap
  · exact hp
  · exact P.transpose_value _ _ hp

theorem produce (U : M.Macro H 1) (N : M.Macro H 4) (c : K) (hc : c≠0)
    (h0 : U.network.denote (fun _=>false)=c) (h1 : U.network.denote (fun _=>true)=0)
    (B : Matrix Bool Bool K) (hN : N.network.denote=P.row B) (cap : C.Cap B) :
    ∃Q : M.Macro H 2, ∃u v : K, u≠0 ∧ v≠0 ∧ C.Infinite (v/u) ∧
      Q.network.denote=binarySignature (OrdinaryTargetInterpolationDiagonal.diagonal u v) := by
  obtain ⟨k,hk,swap,ha,hb,hi⟩:=cap
  refine ⟨P.rowCap U (selected N k swap),c^2*C.Read B k swap false false,
    c^2*C.Read B k swap false true,mul_ne_zero (pow_ne_zero _ hc) ha,
    mul_ne_zero (pow_ne_zero _ hc) hb,?_,?_⟩
  · simpa only [mul_div_mul_left _ _ (pow_ne_zero 2 hc)] using hi
  · exact P.rowCap_value U _ c h0 h1 _ (selected_value N B hN k hk swap)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesSelectedCap
end
