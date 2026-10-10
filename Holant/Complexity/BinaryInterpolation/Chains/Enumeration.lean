import Holant.NetworkTensor

/-! Explicit enumeration avoids a choice of finite index ordering in the chain
compiler. Left vertices and edges precede right vertices and edges. -/
namespace Holant.Complexity.BinaryInterpolation.Chains
variable {K V E : Type*} {n nv ne : ℕ}

/-- Convert finite graph indices using the actual supplied enumerations. -/
def enumerate (N : FiniteNetwork K V E n) (v : V ≃ Fin nv) (e : E ≃ Fin ne) :
    Network K n where
  shape := {
    vertices := nv
    arity := fun i => N.arity (v.symm i)
    edges := ne
    ports := (Equiv.sigmaCongrLeft v.symm).trans
      (N.ports.trans (Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr e (Equiv.refl _)))) }
  vertex := fun i => N.vertex (v.symm i)
  edge := fun i => N.edge (e.symm i)

set_option backward.isDefEq.respectTransparency false in
theorem enumerate_denote [Fintype V] [Fintype E] [CommSemiring K]
    (N : FiniteNetwork K V E n) (v : V ≃ Fin nv) (e : E ≃ Fin ne) :
    (enumerate N v e).denote = N.denote := by
  classical
  funext x
  unfold Network.denote FiniteNetwork.denote
  apply Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.prodCongr e.symm (Equiv.refl Bool)) (Equiv.refl Bool))
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv v.symm
    intro i
    congr 1
    funext j
    dsimp [enumerate, NetworkShape.assignment]
    change Sum.elim x z ((Equiv.sumCongr (Equiv.refl _)
      (Equiv.prodCongr e (Equiv.refl _))) (N.ports ⟨v.symm i, j⟩)) = _
    cases N.ports ⟨v.symm i, j⟩ <;> rfl
  · apply Fintype.prod_equiv e.symm
    intro i
    simp [enumerate]

/-- Explicit finite addition enumerates vertices and edges in left-first order. -/
def tensor {m n : ℕ} (L : Network K m) (R : Network K n) : Network K (m + n) :=
  enumerate (Network.tensorFinite L R) finSumFinEquiv finSumFinEquiv

@[simp] theorem tensor_vertices {m n : ℕ} (L : Network K m) (R : Network K n) :
    (tensor L R).shape.vertices = L.shape.vertices + R.shape.vertices := rfl

@[simp] theorem tensor_edges {m n : ℕ} (L : Network K m) (R : Network K n) :
    (tensor L R).shape.edges = L.shape.edges + R.shape.edges := rfl

theorem tensor_denote [CommSemiring K] {m n : ℕ} (L : Network K m) (R : Network K n) :
    (tensor L R).denote = Signature.tensor L.denote R.denote := by
  rw [tensor, enumerate_denote, ← FiniteNetwork.denote_toNetwork]
  exact Network.denote_tensor L R

end Holant.Complexity.BinaryInterpolation.Chains
