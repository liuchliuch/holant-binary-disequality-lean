import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Basis
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Templates

/-! Zero rates are replaced by one while their basis rows are set to zero.
All positive powers remain exactly the original physical chain. Exponent
zero is precisely the support projector of the original Bell spectrum. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4SupportBasis
open Holant
open scoped BigOperators
namespace B
export GlobalCloseCompletionComplementQ4Basis (basis linear)
end B
namespace S
export GlobalCloseCompletionComplementQ4Series (ofSpectrum row)
end S
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def filled (v : Fin 4→K) (i : Fin 4) : K:=by
  classical
  exact if v i=0 then 1 else v i
def masked (v : Fin 4→K) (i : Fin 4) : Signature K 4:=by
  classical
  exact if v i=0 then 0 else B.basis i
def support (v : Fin 4→K) (i : Fin 4) : K:=by
  classical
  exact if v i=0 then 0 else 1

theorem filled_nonzero (v : Fin 4→K) (i : Fin 4) : filled v i≠0 := by
  classical
  unfold filled
  split_ifs with zero
  · exact one_ne_zero
  · exact zero

theorem positive (v : Fin 4→K) (k : ℕ) (x : Fin 4→Bool) :
    S.ofSpectrum (fun i=>v i^(k+1)) x=∑i,(filled v i)^(k+1)*masked v i x := by
  classical
  rw [B.linear]
  apply Finset.sum_congr rfl
  intro i _
  by_cases zero : v i=0 <;> simp [filled,masked,zero]

theorem zero (v : Fin 4→K) (x : Fin 4→Bool) :
    S.ofSpectrum (support v) x=∑i,masked v i x := by
  classical
  rw [B.linear]
  apply Finset.sum_congr rfl
  intro i _
  by_cases zero : v i=0 <;> simp [support,masked,zero]

theorem rank_three (v : Fin 4→K) (h0 : v 0≠0) (h1 : v 1≠0) (h2 : v 2≠0) (h3 : v 3=0) :
    S.ofSpectrum (support v)=S.row 0 1 ((2:K)⁻¹) ((2:K)⁻¹) := by
  have values : support v=![1,1,1,0] := by
    funext i
    fin_cases i <;> simp [support,h0,h1,h2,h3]
  rw [values]
  simp [S.ofSpectrum]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4SupportBasis
end
