import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationBlocks

/-! Two actual pure Eq4 graphs joined by three native X edges supply a
literal nonzero multiple of X, without installing an equality edge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureXGraph
open Holant Holant.Algebraic Holant.Complexity
namespace T
export GlobalCloseCompletionComplementQ4Templates (connect reindex contract connect_network)
end T
namespace S
export GlobalCloseCompletionComplementQ4Series (row connected)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (N : NativeAntiTargetSource.Output H 4)

def output : NativeAntiTargetSource.Output H 2:=
  T.contract H (T.reindex H (T.connect H N N) (Equiv.swap 1 2))

theorem value (c : K) (form : N.network.denote=S.row c 0 0 0) :
    (output H N).network.denote=fun x=>c^2*Signature.disequality (x 0) (x 1) := by
  change ((T.reindex H (T.connect H N N) (Equiv.swap 1 2)).network.contract Signature.disequality).denote=_
  rw [Network.denote_contract]
  change Signature.contract Signature.disequality
    (Holant.Complexity.BinaryInterpolation.Chains.reindex (T.connect H N N).network (Equiv.swap 1 2)).denote=_
  rw [Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,T.connect_network,
    S.connected _ _ c 0 0 0 c 0 0 0 form form]
  simp only [mul_zero,zero_mul,add_zero,zero_add]
  rw [GlobalCloseCompletionComplementQ4ClassificationReduction.swap_bc]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Signature.contract,S.row,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      Signature.disequality,h0,h1,pow_two]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureXGraph
end
