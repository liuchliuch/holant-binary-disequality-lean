import Holant.Realization
import Holant.Tensor

/-! Same-family permutation of the actual boundary, including free-stub kernel
corrections. This only changes port order, never the vertex resources. -/
namespace Holant.Dihedral.CompatibleClosure
open Holant
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [CommSemiring K] {n : ℕ}

def reorderOpen (N : OpenNetwork K n) (p : Equiv.Perm (Fin n)) : OpenNetwork K n where
  shape := {
    vertices := N.shape.vertices
    arity := N.shape.arity
    free := N.shape.free
    edges := N.shape.edges
    boundary := p.toEmbedding.trans N.shape.boundary
    ends := N.shape.ends
    ordinary_boundary_iff_unpaired := by
      intro q
      rw [← N.shape.ordinary_boundary_iff_unpaired]
      constructor
      · rintro ⟨j,hj⟩
        exact ⟨p j,hj⟩
      · rintro ⟨j,hj⟩
        exact ⟨p.symm j,by simpa using hj⟩
    freeBoundary := fun f => p.symm (N.shape.freeBoundary f)
    free_boundary := by intro f; simpa using N.shape.free_boundary f
    freeEdge := N.shape.freeEdge
    free_paired := N.shape.free_paired }
  vertex := N.vertex
  edge := N.edge

theorem reorderOpen_raw (N : OpenNetwork K n) (p : Equiv.Perm (Fin n)) :
    (reorderOpen N p).raw = Tensor.reindex p.symm N.raw := by
  funext x
  unfold OpenNetwork.raw
  apply Finset.sum_congr rfl
  intro z _
  have he : (∀ j, z ((reorderOpen N p).shape.boundary j) = x j) ↔
      ∀ j, z (N.shape.boundary j) = x (p.symm j) := by
    constructor
    · intro h j
      have hh := h (p.symm j)
      change z (N.shape.boundary (p (p.symm j))) = x (p.symm j) at hh
      simpa only [Equiv.apply_symm_apply] using hh
    · intro h j
      change z (N.shape.boundary (p j)) = x j
      simpa only [Equiv.symm_apply_apply] using h (p j)
  simp only [he]
  rfl

theorem coordinateAction_reindex (A : Fin n → Kernel K) (f : Signature K n)
    (p : Equiv.Perm (Fin n)) :
    Signature.coordinateAction (fun j => A (p j)) (Tensor.reindex p.symm f) =
      Tensor.reindex p.symm (Signature.coordinateAction A f) := by
  funext x
  unfold Signature.coordinateAction Tensor.reindex
  apply Fintype.sum_equiv (Equiv.arrowCongr p (Equiv.refl Bool))
  intro y
  apply congrArg (· * f (fun i => y (p.symm i)))
  apply Fintype.prod_equiv p
  intro j
  simp

theorem reorderOpen_tensor (N : OpenNetwork K n) (p : Equiv.Perm (Fin n)) :
    (reorderOpen N p).tensor = Tensor.reindex p.symm N.tensor := by
  rw [OpenNetwork.tensor,reorderOpen_raw]
  have hk : (reorderOpen N p).boundaryKernel = fun j => N.boundaryKernel (p j) := by
    funext j a b
    simp [reorderOpen,OpenNetwork.boundaryKernel]
    cases N.shape.boundary (p j) <;> rfl
  rw [hk,coordinateAction_reindex]
  rfl

/-- Exact reindexing does not consume a scalar and works for every existing
actual OpenNetwork realization. -/
theorem realizes_reindex (F : SignatureFamily K) (W : EdgeKind) (q : Signature K n)
    (hq : Gadget.Realizes F W q) (p : Equiv.Perm (Fin n)) :
    Gadget.Realizes F W (Tensor.reindex p.symm q) := by
  obtain ⟨N,hN,hW,hq⟩ := hq
  exact ⟨reorderOpen N p,hN,hW,(reorderOpen_tensor N p).trans (congrArg (Tensor.reindex p.symm) hq)⟩

end Holant.Dihedral.CompatibleClosure
