import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput
import Holant.Proofs.Hardness.EightVertexGaugeTwoRowNetwork

/-! Small physical operations used by signed merger synthesis. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeOperations
open Holant Holant.Complexity
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex)
end C
namespace L
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork
  (tensor reindex contract exact_tensor exact_reindex exact_contract)
end L
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature K (a i.val))

def tensor {m n : ℕ} (N : NativeAntiTargetSource.Output H m)
    (M : NativeAntiTargetSource.Output H n) : NativeAntiTargetSource.Output H (m+n) where
  network := C.tensor N.network M.network
  labels := L.tensor N.network M.network N.labels M.labels
  exact := L.exact_tensor N.network M.network N.labels M.labels H N.exact M.exact
  native := by
    intro e
    change Sum.elim N.network.edge M.network.edge (finSumFinEquiv.symm e) = _
    cases finSumFinEquiv.symm e with
    | inl e => exact N.native e
    | inr e => exact M.native e

def reindex {n : ℕ} (N : NativeAntiTargetSource.Output H n) (e : Equiv.Perm (Fin n)) :
    NativeAntiTargetSource.Output H n where
  network := C.reindex N.network e
  labels := L.reindex N.network N.labels e
  exact := L.exact_reindex N.network N.labels H N.exact e
  native := N.native

def contract {n : ℕ} (N : NativeAntiTargetSource.Output H (n+2)) :
    NativeAntiTargetSource.Output H n where
  network := N.network.contract Signature.disequality
  labels := L.contract N.network N.labels 0 Signature.disequality
  exact := L.exact_contract H N.network N.labels N.exact 0 Signature.disequality
  native := by intro e; exact Fin.cases rfl (fun e => N.native e) e

def connect (N M : NativeAntiTargetSource.Output H 4) : NativeAntiTargetSource.Output H 4 :=
  contract H (n:=4) (contract H (n:=6) (reindex H (n:=8) (tensor H (m:=4) (n:=4) N M)
    (Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork.order false)))

theorem connect_network (N M : NativeAntiTargetSource.Output H 4) :
    (connect H N M).network =
      Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork.connect N.network M.network false := rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeOperations
end
