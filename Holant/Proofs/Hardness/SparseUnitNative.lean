import Holant.Proofs.Hardness.SparseUnitLocal

/-! Actual edge labels and graph sizes of the thin original-M unit macros. -/
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseUnitNative
open Holant Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open SparseUnitLocal
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex)
end Chain
variable {K : Type*} [Field K]

def Native {n : ℕ} (N : Network K n) : Prop := ∀e,N.edge e=Signature.disequality

private theorem native_corolla {n : ℕ} (f : Signature K n) : Native (Network.corolla f) :=
  fun e => Fin.elim0 e

private theorem native_tensor {m n : ℕ} (N : Network K m) (B : Network K n)
    (hN : Native N) (hB : Native B) : Native (Chain.tensor N B) := by
  intro e
  change Sum.elim N.edge B.edge (finSumFinEquiv.symm e)=Signature.disequality
  cases finSumFinEquiv.symm e with
  | inl e => exact hN e
  | inr e => exact hB e

private theorem native_contract {n : ℕ} (N : Network K (n+2))
    (hN : Native N) : Native (N.contract Signature.disequality) := by
  intro e
  exact Fin.cases rfl (fun e => hN e) e

theorem cube_native (M : Signature K 4) (one : Bool) : Native (cube M one) := by
  apply native_contract
  intro e
  change Sum.elim (nativeChain M).edge (Network.corolla (pin (K:=K) (!one))).edge
    ((Fintype.equivFin (Fin 2 ⊕ Fin 0)).symm e)=Signature.disequality
  cases (Fintype.equivFin (Fin 2 ⊕ Fin 0)).symm e with
  | inl e => exact nativeChain_edge M e
  | inr e => exact Fin.elim0 e

private theorem pinNetwork_native (one : Bool) (N : Network K 3) (hN : Native N) :
    Native (pinNetwork one N) :=
  native_contract _ (native_tensor N _ hN (native_corolla _))

theorem binary_native (M : Signature K 4) (one : Bool) : Native (binary M one) :=
  pinNetwork_native one _ (cube_native M one)

theorem third_native (M : Signature K 4) : Native (third M) :=
  pinNetwork_native false _ (cube_native M false)

private theorem attach_native (N : Network K 3) (B : Network K 2)
    (hN : Native N) (hB : Native B) (i : Fin 3) : Native (attach N B i) :=
  native_contract _ (native_tensor N B hN hB)

private theorem native_swap (B : Network K 2) (hB : Native B) : Native (swap B) := hB

section
attribute [local irreducible] cube binary third attach swap

theorem unit_native (M : Signature K 4) (one : Bool) : Native (unitNetwork M one) := by
  cases one
  · exact attach_native (attach (cube M false) (third M) 0) (swap (binary M false))
      (attach_native (cube M false) (third M) (cube_native M false) (third_native M) 0)
      (native_swap (binary M false) (binary_native M false)) 2
  · exact attach_native (attach (cube M true) (binary M false) 0) (binary M true)
      (attach_native (cube M true) (binary M false) (cube_native M true) (binary_native M false) 0)
      (binary_native M true) 1

end

theorem cube_counts (M : Signature K 4) (one : Bool) :
    (cube M one).shape.vertices=3 ∧ (cube M one).shape.edges=3 := by
  simp [cube,pinned,Holant.Certificates.FourthRootOdd.reorderNetwork,Network.contract,
    Network.tensor_vertices,Network.tensor_edges,nativeChain_vertices,nativeChain_edges,Network.corolla]

theorem binary_counts (M : Signature K 4) (one : Bool) :
    (binary M one).shape.vertices=4 ∧ (binary M one).shape.edges=4 := by
  have h := cube_counts M one
  change (cube M one).shape.vertices+1=4 ∧ (cube M one).shape.edges+0+1=4
  omega

theorem third_counts (M : Signature K 4) :
    (third M).shape.vertices=4 ∧ (third M).shape.edges=4 := by
  have h := cube_counts M false
  change (cube M false).shape.vertices+1=4 ∧ (cube M false).shape.edges+0+1=4
  omega

theorem unit_counts (M : Signature K 4) (one : Bool) :
    (unitNetwork M one).shape.vertices=11 ∧ (unitNetwork M one).shape.edges=13 := by
  have h0 := cube_counts M false
  have h1 := cube_counts M true
  have hb0 := binary_counts M false
  have hb1 := binary_counts M true
  have ht := third_counts M
  cases one
  · change (cube M false).shape.vertices+(third M).shape.vertices+(binary M false).shape.vertices=11 ∧
      ((cube M false).shape.edges+(third M).shape.edges+1)+(binary M false).shape.edges+1=13
    omega
  · change (cube M true).shape.vertices+(binary M false).shape.vertices+(binary M true).shape.vertices=11 ∧
      ((cube M true).shape.edges+(binary M false).shape.edges+1)+(binary M true).shape.edges+1=13
    omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseUnitNative
