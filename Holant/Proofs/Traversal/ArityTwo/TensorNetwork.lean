import Holant.Proofs.Traversal.ArityTwo.SourceExpansion
import Holant.NetworkGluing.Finite
import Mathlib.Data.Fintype.BigOperators


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorNetwork
open Holant Holant.Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Data (K : Type) (n : ℕ) where
  count : ℕ
  arity : Fin count → ℕ
  factor : (i : Fin count) → Signature K (arity i)
  ports : (Σ i : Fin count, Fin (arity i)) ≃ Fin n
  scalar : K

namespace Data
variable {K : Type} {n : ℕ}
def value [CommMonoid K] (D : Data K n) : Signature K n :=
  fun x => D.scalar * ∏ i, D.factor i (fun j => x (D.ports ⟨i,j⟩))

def ofDecomposition [Monoid K] (D : TensorDecomposition K n) : Data K n :=
  ⟨D.count,D.arity,D.factor,D.ports,(D.scale : K)⟩

def zero [Zero K] [One K] (n : ℕ) : Data K n where
  count := n
  arity := fun _ => 1
  factor := fun _ _ => 1
  ports := {
    toFun := Sigma.fst
    invFun := fun i => ⟨i,0⟩
    left_inv := by rintro ⟨i,j⟩; have hj : j = 0 := Fin.eq_zero j; subst j; rfl
    right_inv := fun _ => rfl }
  scalar := 0

@[simp] theorem zero_value [CommSemiring K] : (zero (K := K) n).value = 0 := by
  funext x
  simp [value,zero]

abbrev Vertex (D : Data K n) := Option (Fin D.count)
def vertexArity (D : Data K n) : D.Vertex → ℕ
  | none => 0
  | some i => D.arity i

def factorPorts (D : Data K n) :
    (Σ v : D.Vertex, Fin (D.vertexArity v)) ≃ (Σ i : Fin D.count, Fin (D.arity i)) where
  toFun p := match p with
    | ⟨none,j⟩ => Fin.elim0 j
    | ⟨some i,j⟩ => ⟨i,j⟩
  invFun p := ⟨some p.1,p.2⟩
  left_inv := by rintro ⟨v,j⟩; cases v with
    | none => exact Fin.elim0 j
    | some i => rfl
  right_inv := fun _ => rfl

def finite (D : Data K n) : FiniteNetwork K D.Vertex Empty n where
  arity := D.vertexArity
  ports := (D.factorPorts.trans D.ports).trans (Equiv.sumEmpty (Fin n) (Empty × Bool)).symm
  vertex := fun v => match v with
    | none => fun _ => D.scalar
    | some i => D.factor i
  edge := Empty.elim

theorem finite_denote [CommSemiring K] (D : Data K n) : D.finite.denote = D.value := by
  classical
  funext x
  simp [FiniteNetwork.denote,finite,value,vertexArity,factorPorts,
    Fintype.prod_option,Equiv.sumEmpty]

def network (D : Data K n) : Network K n := D.finite.toNetwork

theorem network_denote [CommSemiring K] (D : Data K n) : D.network.denote = D.value := by
  rw [network,FiniteNetwork.denote_toNetwork,D.finite_denote]

theorem network_arity (D : Data K n) (hd : ∀ j, D.arity j ≤ 2)
    (v : Fin D.network.shape.vertices) : D.network.shape.arity v ≤ 2 := by
  change D.vertexArity ((Fintype.equivFin D.Vertex).symm v) ≤ 2
  cases (Fintype.equivFin D.Vertex).symm v with
  | none => exact Nat.zero_le _
  | some i => exact hd i
end Data

variable {n : ℕ} (f : Signature AlgebraicComplex n)
variable (hf : SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) f)

def ofSource : Data AlgebraicComplex n :=
  if hz : f = 0 then Data.zero n
  else Data.ofDecomposition (Classical.choose (SourceExpansion.decomposition_of_nonzero hf hz))

theorem ofSource_exact : (ofSource f hf).value = f := by
  unfold ofSource
  split
  · rename_i hz
    rw [Data.zero_value,hz]
  · rename_i hz
    exact (Classical.choose_spec (SourceExpansion.decomposition_of_nonzero hf hz)).2

theorem ofSource_arity (j : Fin (ofSource f hf).count) : (ofSource f hf).arity j ≤ 2 := by
  have hd : ∀ (d : Data AlgebraicComplex n), d = ofSource f hf → ∀ j, d.arity j ≤ 2 := by
    intro d he
    by_cases hz : f = 0
    · have he' : d = Data.zero n := he.trans (dif_pos hz)
      clear he
      subst d
      intro j
      exact Nat.le_succ _
    · have he' : d = Data.ofDecomposition
          (Classical.choose (SourceExpansion.decomposition_of_nonzero hf hz)) := he.trans (dif_neg hz)
      clear he
      subst d
      intro j
      rcases (Classical.choose_spec (SourceExpansion.decomposition_of_nonzero hf hz)).1 j with h | h <;>
        change (Classical.choose (SourceExpansion.decomposition_of_nonzero hf hz)).arity j ≤ 2 <;> omega
  exact hd _ rfl j

theorem ofSource_network : (ofSource f hf).network.denote = f :=
  (Data.network_denote _).trans (ofSource_exact f hf)

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorNetwork
