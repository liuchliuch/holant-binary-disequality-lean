import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryDenseOrbit

/-! Exact ordinary two-copy parity-block square, with the actual crossed
wire order corrected by swapping the right copy's first two ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinarySquare
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (series seriesLabels series_exact series_ordinary)
end P
namespace C
export BinaryInterpolation.Chains (reindex reindex_denote tensor_denote)
end C
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace M
export GeneralEOAffinePlaneChain (seriesOrder)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))

def square (N : Macro H 4) : Macro H 4 where
  network := P.series N.network (N.reindex (Equiv.swap 0 1)).network
  labels := P.seriesLabels N.network N.labels _ (N.reindex (Equiv.swap 0 1)).labels
  exact := P.series_exact H N.network N.labels _ (N.reindex (Equiv.swap 0 1)).labels
    N.exact (N.reindex (Equiv.swap 0 1)).exact
  edges := P.series_ordinary N.network _ N.edges (N.reindex (Equiv.swap 0 1)).edges

theorem square_normal (N : Macro H 4) (a b c d : K) (form : N.network.denote=T.normal a b c d) :
    (square H N).network.denote=T.normal (a^2+b^2) (2*a*b) (c^2+d^2) (2*c*d) := by
  funext x
  change (P.series N.network (C.reindex N.network (Equiv.swap 0 1))).denote x=_
  rw [P.series,Network.denote_contract_equality,Network.denote_contract_equality,
    Network.denote_contract_equality,C.reindex_denote,C.tensor_denote,C.reindex_denote,form]
  have eval (u v w z : Bool) :
      Tensor.reindex M.seriesOrder ((T.normal a b c d).tensor
        (Tensor.reindex (Equiv.swap 0 1) (T.normal a b c d)))
        (Fin.cons u (Fin.cons v (Fin.cons w (Fin.cons z x))))=
      T.normal a b c d ![x 0,x 1,u,w]*T.normal a b c d ![v,z,x 2,x 3] := by
    simp only [Tensor.reindex_apply,Signature.tensor_apply]
    congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl
  rw [eval,eval,eval,eval]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinarySquare
end
