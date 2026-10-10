import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinarySquare
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryHadamard

/-! Four actual ordinary EO-pair copies and retained Z vertices give scalar
Eq4 with coefficient p⁴-q⁴. The first two copies form the literal symmetric
equality pair(p²,q²), with both original boundary permutations recorded. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPairEq4
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace S
export GlobalCloseCompletionC2OrdinarySquare (square square_normal)
end S
namespace O
export GlobalCloseCompletionC2OrdinaryDenseOrbit (swap_bc)
end O
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric zSignature network labels exact ordinary denote)
end P
namespace M
export GeneralEOAffinePlaneChain (binary)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {a : ℕ→ℕ}
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable (H : (i : Fin s)→Signature K (a i.val))
variable (N : Macro H 4)

def pairMacro : Macro H 4 := N.reindex (Equiv.swap 1 2)

theorem pair_form (p q : K) (form : N.network.denote=T.normal p 0 q 0) :
    (pairMacro H N).network.denote=P.pair (M.binary (P.symmetric p q)) := by
  rw [pairMacro,Macro.reindex_denote,form,O.swap_bc,GlobalCloseCompletionC2OrdinaryHadamard.normal_pair]

variable (z : Fin s) (literal : (⟨a z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

include literal in
theorem z_literal : (⟨a z.val,H z⟩ : AnySignature K)=⟨2,P.zSignature 1⟩ := by
  exact literal.trans (congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K))
    (by funext x; change T.Z (x 0) (x 1)=1*T.Z (x 0) (x 1); rw [one_mul]))

def graph : Macro H 4 where
  network := P.network (pairMacro H N).network 1
  labels := P.labels H _ (pairMacro H N).labels z 1 (z_literal H z literal)
  exact := P.exact H _ (pairMacro H N).labels z 1 (z_literal H z literal) (pairMacro H N).exact
  edges := P.ordinary (pairMacro H N).network 1 (pairMacro H N).edges

theorem graph_denote (p q : K) (form : N.network.denote=T.normal p 0 q 0) :
    (graph H N z literal).network.denote=(p^2-q^2) • Holant.EightVertex.ProductAnchor.equalityFour := by
  have h := P.denote (pairMacro H N).network 1 p q (pair_form H N p q form)
  change (P.network (pairMacro H N).network 1).denote=_
  simpa only [one_pow,one_mul] using h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPairEq4
end
