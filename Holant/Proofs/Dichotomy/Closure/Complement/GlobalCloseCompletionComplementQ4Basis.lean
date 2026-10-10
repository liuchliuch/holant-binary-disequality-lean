import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Series

/-! The four literal Bell components form the actual entrywise linear
expansion used by the network recovery theorem. The two even components
factor as nonzero scalar products of nonsingular diagonal binaries. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Basis
open Holant
open scoped BigOperators
namespace S
export GlobalCloseCompletionComplementQ4Series
  (ofSpectrum spectrum row reconstruct first_projector second_projector diagonal)
end S
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def basis (j : Fin 4) : Signature K 4:=S.ofSpectrum (Pi.single j 1)

theorem linear (v : Fin 4→K) (x : Fin 4→Bool) :
    S.ofSpectrum v x=∑i,v i*basis i x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.ofSpectrum,S.row,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      basis,Fin.sum_univ_four,Pi.single_apply,h0,h1,h2,h3] <;> ring

theorem first : (basis 0 : Signature K 4)=fun x=>(2:K)⁻¹*Signature.tensor (S.diagonal 1) (S.diagonal 1) x := by
  have vector : (Pi.single (0 : Fin 4) (1:K))=![1,0,0,0] := by
    funext i
    fin_cases i <;> simp [Pi.single_apply]
  rw [basis,vector]
  exact S.first_projector
theorem second : (basis 1 : Signature K 4)=fun x=>-(2:K)⁻¹*Signature.tensor (S.diagonal (-1)) (S.diagonal (-1)) x := by
  have vector : (Pi.single (1 : Fin 4) (1:K))=![0,1,0,0] := by
    funext i
    fin_cases i <;> simp [Pi.single_apply]
  rw [basis,vector]
  exact S.second_projector


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Basis
end
