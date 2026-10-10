import Holant.Proofs.Hardness.DenseEOUnitLocal
import Holant.Proofs.Hardness.SparseUnitNative

/-! Exact native-X edges and finite sizes of the same-q dense EO macros. -/
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseEOUnitNative
open Holant Holant.Complexity
open DenseEOUnitLocal
namespace U
export SparseUnitLocal (pin pinNetwork attach)
end U
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex)
end Chain
export SparseUnitNative (Native)
variable {K : Type*} [Field K]

private theorem native_corolla {n : ℕ} (f : Signature K n) : Native (Network.corolla f) := fun e=>Fin.elim0 e
private theorem native_tensor {m n : ℕ} (N : Network K m) (B : Network K n)
    (hN : Native N) (hB : Native B) : Native (Chain.tensor N B) := by
  intro e
  change Sum.elim N.edge B.edge (finSumFinEquiv.symm e)=Signature.disequality
  cases finSumFinEquiv.symm e with
  | inl e=>exact hN e
  | inr e=>exact hB e
private theorem native_contract {n : ℕ} (N : Network K (n+2)) (hN : Native N) :
    Native (N.contract Signature.disequality) := by
  intro e
  exact Fin.cases rfl (fun e=>hN e) e

theorem cube_native (q : Signature K 4) (one : Bool) : Native (cube q one) := by
  apply native_contract
  intro e
  change Sum.elim (Chain.reindex (Network.corolla q) (cubeOrder one)).edge
    (Network.corolla (U.pin (!one))).edge ((Fintype.equivFin (Fin 0 ⊕ Fin 0)).symm e)=Signature.disequality
  cases (Fintype.equivFin (Fin 0 ⊕ Fin 0)).symm e with
  | inl e=>exact Fin.elim0 e
  | inr e=>exact Fin.elim0 e

private theorem pinNetwork_native (one : Bool) (N : Network K 3) (hN : Native N) :
    Native (U.pinNetwork one N) := native_contract _ (native_tensor N _ hN (native_corolla _))

theorem binary0_native (q : Signature K 4) (one : Bool) : Native (binary0 q one) :=
  pinNetwork_native one _ (cube_native q one)
theorem binary1_native (q : Signature K 4) (one : Bool) : Native (binary1 q one) :=
  pinNetwork_native one _ (cube_native q one)

private theorem attach_native (N : Network K 3) (B : Network K 2)
    (hN : Native N) (hB : Native B) (i : Fin 3) : Native (U.attach N B i) :=
  native_contract _ (native_tensor N B hN hB)

section
attribute [local irreducible] cube binary0 binary1 SparseUnitLocal.attach

theorem unit_native (q : Signature K 4) (one : Bool) : Native (unitNetwork q one) :=
  attach_native (U.attach (cube q one) (binary0 q one) 0) (binary1 q one)
    (attach_native (cube q one) (binary0 q one) (cube_native q one) (binary0_native q one) 0)
    (binary1_native q one) 1
end

theorem cube_counts (q : Signature K 4) (one : Bool) :
    (cube q one).shape.vertices=2 ∧ (cube q one).shape.edges=1 := by
  simp [cube,SparseUnitLocal.pinned,Holant.Certificates.FourthRootOdd.reorderNetwork,
    Network.contract,Network.tensor_vertices,Network.tensor_edges,Network.corolla,Chain.reindex]

theorem binary0_counts (q : Signature K 4) (one : Bool) :
    (binary0 q one).shape.vertices=3 ∧ (binary0 q one).shape.edges=2 := by
  have h := cube_counts q one
  change (cube q one).shape.vertices+1=3 ∧ (cube q one).shape.edges+0+1=2
  omega

theorem binary1_counts (q : Signature K 4) (one : Bool) :
    (binary1 q one).shape.vertices=3 ∧ (binary1 q one).shape.edges=2 := by
  have h := cube_counts q one
  change (cube q one).shape.vertices+1=3 ∧ (cube q one).shape.edges+0+1=2
  omega

theorem unit_counts (q : Signature K 4) (one : Bool) :
    (unitNetwork q one).shape.vertices=8 ∧ (unitNetwork q one).shape.edges=7 := by
  have hq := cube_counts q one
  have h0 := binary0_counts q one
  have h1 := binary1_counts q one
  change (cube q one).shape.vertices+(binary0 q one).shape.vertices+(binary1 q one).shape.vertices=8 ∧
    ((cube q one).shape.edges+(binary0 q one).shape.edges+1)+(binary1 q one).shape.edges+1=7
  omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseEOUnitNative
