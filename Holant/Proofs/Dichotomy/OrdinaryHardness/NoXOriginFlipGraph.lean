import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalMergeGraphs

/-! Attach an actual weighted antidiagonal at any selected external port.
The two boundary permutations are literal reindexings of the same graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginFlipGraph
open Holant Holant.Tractable
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
export OrdinaryNegativeCubicGadgets.Macro (reindex reindex_denote)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {arity : ℕ→ℕ}
variable {H : (j : Fin s)→Signature K (arity j.val)}

def flipAt (i : Fin (n+2)) (x : Fin (n+2)→Bool) : Fin (n+2)→Bool :=
  Function.update x i (!(x i))

def graph (N : M.Macro H (n+2)) (A : M.Macro H 2) (i : Fin (n+2)) : M.Macro H (n+2) :=
  (NoXLocalMergeGraphs.flipFirst (N.reindex (Equiv.swap 0 i)) A).reindex (Equiv.swap 0 i)

theorem graph_value (N : M.Macro H (n+2)) (A : M.Macro H 2) (i : Fin (n+2))
    (v w : K) (anti : A.network.denote=NoXWeightedAntiSigned.anti v w)
    (x : Fin (n+2)→Bool) :
    (graph N A i).network.denote x=(if x i then v else w)*N.network.denote (flipAt i x) := by
  rw [graph,M.reindex_denote]
  simp only [Tensor.reindex_apply]
  rw [NoXLocalMergeGraphs.flipFirst_value _ A v w anti,M.reindex_denote]
  simp only [Tensor.reindex_apply,Equiv.swap_apply_left]
  congr 1
  apply congrArg N.network.denote
  funext j
  by_cases hj : j=i
  · subst j
    simp [flipAt,Equiv.swap_apply_right]
  by_cases hz : j=0
  · subst j
    have hi : i≠0 := Ne.symm hj
    obtain ⟨k,rfl⟩ := Fin.exists_succ_eq.mpr hi
    simp [flipAt,Equiv.swap_apply_left,Equiv.swap_apply_right,Fin.cons,hj]
  · have hi : Equiv.swap (0 : Fin (n+2)) i j=j := Equiv.swap_apply_of_ne_of_ne hz hj
    rw [hi]
    rcases j with ⟨j,hj'⟩
    cases j with
    | zero => exact False.elim (hz rfl)
    | succ j =>
      change x (Equiv.swap (0 : Fin (n+2)) i ⟨j+1,hj'⟩)=_
      rw [hi]
      simp [flipAt,hj]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginFlipGraph
end
