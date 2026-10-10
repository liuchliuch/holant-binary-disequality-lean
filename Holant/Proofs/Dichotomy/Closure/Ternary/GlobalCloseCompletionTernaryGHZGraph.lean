import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZCore

/-! The three-copy cyclic symmetrizer is an actual ordinary graph over the
same original labels. Its six internal ports form three equality edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZGraph
open Holant
open scoped BigOperators
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (tensor reindex contract tensor_denote reindex_denote contract_denote)
end M
namespace T
export GlobalCloseCompletionTernaryGHZCore (triangle)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false

def ports : Equiv.Perm (Fin 9) := Equiv.ofBijective
  (![6,0,4,7,2,1,8,5,3] : Fin 9→Fin 9) (by decide)

variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (a i.val)} (N : M.Macro H 3)

def raw : M.Macro H 9 := (N.tensor (N.tensor N)).reindex ports

def triangle : M.Macro H 3 := ((raw N).contract.contract).contract

theorem raw_value (i j k : Bool) (x : Fin 3→Bool) :
    (raw N).network.denote (Fin.cons i (Fin.cons i (Fin.cons j (Fin.cons j (Fin.cons k (Fin.cons k x))))))=
      N.network.denote ![x 0,i,k]*N.network.denote ![x 1,j,i]*N.network.denote ![x 2,k,j] := by
  simp only [raw,M.reindex_denote,M.tensor_denote,Tensor.reindex_apply,Signature.tensor_apply,ports,Equiv.ofBijective_apply]
  rw [mul_assoc]
  congr 1
  · congr 1
    funext q
    fin_cases q <;> rfl
  · congr 1
    · congr 1
      funext q
      fin_cases q <;> rfl
    · congr 1
      funext q
      fin_cases q <;> rfl

theorem value : (triangle N).network.denote=T.triangle N.network.denote := by
  funext x
  simp only [triangle,M.contract_denote,raw_value,T.triangle,Fintype.sum_bool]
  ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZGraph
end
