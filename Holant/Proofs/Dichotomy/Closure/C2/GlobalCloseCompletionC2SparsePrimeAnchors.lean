import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4PrimeTools
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSparseEq4
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryEOEq4
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPairEq4

/-! Every prime sparse canonical q4 has a genuine same-source Eq4 graph.
The determinant exclusions are proved from original-field tensor primality,
and all graph scalars remain explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SparsePrimeAnchors
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace O
export GlobalCloseCompletionC2OrdinaryDenseOrbit (swap_bc swap_bd)
end O
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (zSignature)
end P
namespace Q
export GlobalCloseCompletionC2Q4PrimeTools (prime_reindex pair_det eo_det signed_sum)
end Q
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed)
end S
namespace W
export GlobalCloseCompletionC2OrdinaryTwist (eq4Graph eq4Labels eq4_exact eq4_ordinary eq4Graph_denote)
end W
namespace E
export GlobalCloseCompletionC2OrdinaryPairOutcome (HasEq4)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {r : ℕ} {b : ℕ→ℕ}
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable (H : (i : Fin r)→Signature K (b i.val))
variable (z : Fin r) (literal : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

theorem reindex_prime (N : Macro H 4) (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) (e : Equiv.Perm (Fin 4)) :
    Prime (⟨4,(N.reindex e).network.denote⟩ : AnySignature K) := by
  rw [Macro.reindex_denote]
  exact Q.prime_reindex _ prime e

include literal in
theorem pair (N : Macro H 4) (A D : K) (form : N.network.denote=T.normal A 0 0 D)
    (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) : E.HasEq4 H := by
  have det := Q.pair_det A D (form ▸ prime)
  let N' := (N.reindex (Equiv.swap 1 3)).reindex (Equiv.swap 1 2)
  have hN : N'.network.denote=T.normal A 0 D 0 := by
    rw [Macro.reindex_denote,Macro.reindex_denote,form,O.swap_bd,O.swap_bc]
  exact ⟨GlobalCloseCompletionC2OrdinaryPairEq4.graph H N' z literal,A^2-D^2,sub_ne_zero.mpr det,
    GlobalCloseCompletionC2OrdinaryPairEq4.graph_denote H N' z literal A D hN⟩

include literal in
theorem eo (N : Macro H 4) (C D : K) (form : N.network.denote=T.normal 0 0 C D)
    (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) : E.HasEq4 H := by
  have det := Q.eo_det C D (form ▸ prime)
  have zLiteral : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,P.zSignature 1⟩ :=
    GlobalCloseCompletionC2OrdinaryEOEq4.z_literal H z literal
  let Q : Macro H 4 := {
    network := W.eq4Graph N.network 1
    labels := W.eq4Labels H N.network N.labels z 1 zLiteral
    exact := W.eq4_exact H N.network N.labels z 1 zLiteral N.exact
    edges := W.eq4_ordinary N.network 1 N.edges }
  refine ⟨Q,-(C^2-D^2)^2,neg_ne_zero.mpr (pow_ne_zero _ (sub_ne_zero.mpr det)),?_⟩
  have h := W.eq4Graph_denote N.network 1 0 0 C D form
  simpa only [one_pow,zero_pow (by decide : (2:ℕ)≠0),sub_zero,zero_sub,one_mul] using h

theorem signed (N : Macro H 4) (B C : K) (form : N.network.denote=S.signed B C 0)
    (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K)) : E.HasEq4 H := by
  have sum := Q.signed_sum B C (form ▸ prime)
  exact ⟨GlobalCloseCompletionC2SignedSparseEq4.graph H N,(B^2+C^2)^2,pow_ne_zero _ sum,
    GlobalCloseCompletionC2SignedSparseEq4.graph_denote H N B C form⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SparsePrimeAnchors
end
