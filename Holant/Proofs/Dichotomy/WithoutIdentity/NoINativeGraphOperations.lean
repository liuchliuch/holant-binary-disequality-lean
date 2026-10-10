import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput

/-! Literal original-labelled native tensor, coordinate permutation and X
contraction, independent of interpolation and classification sources. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Templates
open Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace A
export NativeAntiTargetSource (Output template_exact)
end A
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex)
end C
namespace L
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork
  (tensor reindex contract exact_tensor exact_reindex exact_contract count count_tensor count_reindex count_contract)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (b i.val))

def tensor {m n : ℕ} (N : A.Output H m) (M : A.Output H n) : A.Output H (m+n) where
  network:=C.tensor N.network M.network
  labels:=L.tensor N.network M.network N.labels M.labels
  exact:=L.exact_tensor N.network M.network N.labels M.labels H N.exact M.exact
  native:=by
    intro e
    change Sum.elim N.network.edge M.network.edge (finSumFinEquiv.symm e)=_
    cases finSumFinEquiv.symm e with
    | inl e=>exact N.native e
    | inr e=>exact M.native e
def reindex {n : ℕ} (N : A.Output H n) (p : Equiv.Perm (Fin n)) : A.Output H n where
  network:=C.reindex N.network p
  labels:=L.reindex N.network N.labels p
  exact:=L.exact_reindex N.network N.labels H N.exact p
  native:=N.native
def contract {n : ℕ} (N : A.Output H (n+2)) : A.Output H n where
  network:=N.network.contract Signature.disequality
  labels:=L.contract N.network N.labels 0 Signature.disequality
  exact:=L.exact_contract H N.network N.labels N.exact 0 Signature.disequality
  native:=by
    intro e
    exact Fin.cases rfl (fun e=>N.native e) e


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Templates
end
