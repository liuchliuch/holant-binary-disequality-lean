import Holant.ReedMuller.FlatNetwork.BoundaryExpansion
import Holant.ReedMuller.FlatNetwork.FilteredCollection

/-! Eliminate the boundary-word sum exactly, retaining the correction kernel
at every paired free stub. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem tensor_boundary_sum (N : OpenNetwork ℂ n) (x : Fin n → Bool) :
    N.tensor x=∑ z : OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool,
      (∏ j,N.boundaryKernel j (x j) (z (N.shape.boundary j)))*N.weight z := by
  unfold OpenNetwork.tensor Signature.coordinateAction OpenNetwork.raw
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have hb (y : Fin n → Bool) : (∀ j,z (N.shape.boundary j)=y j) ↔ y=(fun j => z (N.shape.boundary j)) := by
    constructor
    · intro h;funext j;exact (h j).symm
    · rintro rfl;exact fun _ => rfl
  simp only [hb,mul_ite,mul_zero]
  simp

abbrev OrdinaryBoundary (s : OpenNetworkShape n) := {j : Fin n // ∃ p,s.boundary j=.inl p}

def boundaryPartitionMap (s : OpenNetworkShape n) : OrdinaryBoundary s ⊕ Fin s.free → Fin n
  | .inl j => j.val
  | .inr f => s.freeBoundary f

theorem boundaryPartition_bijective (s : OpenNetworkShape n) : Function.Bijective (boundaryPartitionMap s) := by
  constructor
  · rintro (j|f) (k|g) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · obtain ⟨p,hp⟩ := j.property
      have hh : s.boundary j.val=s.boundary (s.freeBoundary g) := congrArg s.boundary h
      rw [hp,s.free_boundary] at hh
      cases hh
    · obtain ⟨p,hp⟩ := k.property
      have hh : s.boundary (s.freeBoundary f)=s.boundary k.val := congrArg s.boundary h
      rw [hp,s.free_boundary] at hh
      cases hh
    · exact congrArg Sum.inr (s.freeBoundary_injective h)
  · intro j
    cases hb : s.boundary j with
    | inl p => exact ⟨.inl ⟨j,p,hb⟩,rfl⟩
    | inr f => exact ⟨.inr f,s.boundary.injective ((s.free_boundary f).trans hb.symm)⟩

def boundaryPartition (s : OpenNetworkShape n) : OrdinaryBoundary s ⊕ Fin s.free ≃ Fin n :=
  Equiv.ofBijective (boundaryPartitionMap s) (boundaryPartition_bijective s)

def ordinaryAgrees (s : OpenNetworkShape n) (x : Fin n → Bool)
    (z : OpenPorts s.vertices s.arity s.free → Bool) : Prop :=
  ∀ j : OrdinaryBoundary s,z (s.boundary j.val)=x j.val

def freeBoundaryProduct (N : OpenNetwork ℂ n) (x : Fin n → Bool)
    (z : OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool) : ℂ :=
  ∏ f,(N.edge (N.shape.freeEdge f).1).value (x (N.shape.freeBoundary f)) (z (.inr f))

theorem boundary_kernel_product (N : OpenNetwork ℂ n) (x : Fin n → Bool)
    (z : OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool) :
    (∏ j,N.boundaryKernel j (x j) (z (N.shape.boundary j)))=
      (if ordinaryAgrees N.shape x z then 1 else 0)*freeBoundaryProduct N x z := by
  rw [←(boundaryPartition N.shape).prod_comp,Fintype.prod_sum_type]
  have ho (j : OrdinaryBoundary N.shape) : N.boundaryKernel ((boundaryPartition N.shape) (.inl j))=
      (Signature.equality : Kernel ℂ) := by
    obtain ⟨p,hp⟩ := j.property
    change N.boundaryKernel j.val=_
    simp [OpenNetwork.boundaryKernel,hp]
  have hf (f : Fin N.shape.free) : N.boundaryKernel ((boundaryPartition N.shape) (.inr f))=
      ((N.edge (N.shape.freeEdge f).1).value : Kernel ℂ) := by
    change N.boundaryKernel (N.shape.freeBoundary f)=_
    simp [OpenNetwork.boundaryKernel,N.shape.free_boundary]
  simp only [ho,hf]
  change (∏ j : OrdinaryBoundary N.shape,Signature.equality (x j.val) (z (N.shape.boundary j.val)))*
    (∏ f,(N.edge (N.shape.freeEdge f).1).value (x (N.shape.freeBoundary f))
      (z (N.shape.boundary (N.shape.freeBoundary f))))=_
  simp only [N.shape.free_boundary]
  congr 1
  simp only [Signature.equality,Fintype.prod_boole,ordinaryAgrees]
  have hh : (∀ i : OrdinaryBoundary N.shape,x i.val=z (N.shape.boundary i.val)) ↔
      (∀ i : OrdinaryBoundary N.shape,z (N.shape.boundary i.val)=x i.val) := forall_congr' (fun _ => eq_comm)
  simp only [hh]
  split_ifs <;> rfl

theorem tensor_filtered_boundary_sum (N : OpenNetwork ℂ n) (x : Fin n → Bool) :
    N.tensor x=∑ z : OpenPorts N.shape.vertices N.shape.arity N.shape.free → Bool,
      if ordinaryAgrees N.shape x z then freeBoundaryProduct N x z*N.weight z else 0 := by
  rw [tensor_boundary_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [boundary_kernel_product]
  split_ifs <;> simp

end
end Holant.ReedMuller.FlatNetwork
