import Holant.NetworkTensor
import Holant.NetworkContraction

/-! Ordinary finite networks needed for the literal two-copy certificate.
All supplied vertices and native edges remain explicit; boundary relabelling
changes only the external incidence order. -/
namespace Holant.Certificates.FourthRootOdd
open Holant

def singleVertexNetwork {K : Type*} {n : ℕ} (f : Signature K n) : Network K n where
  shape := {
    vertices := 1
    arity := fun _ => n
    edges := 0
    ports := {
      toFun q := .inl q.2
      invFun q := Sum.elim (fun i => ⟨0,i⟩) (fun q => Fin.elim0 q.1) q
      left_inv q := by
        rcases q with ⟨v,i⟩
        have hv : v=0 := Subsingleton.elim _ _
        subst v
        rfl
      right_inv q := by
        cases q with
        | inl i => rfl
        | inr q => exact Fin.elim0 q.1 } }
  vertex := fun _ => f
  edge := fun e => Fin.elim0 e

def reorderNetwork {K : Type*} {n : ℕ} (N : Network K n) (e : Equiv.Perm (Fin n)) : Network K n where
  shape := {N.shape with ports := N.shape.ports.trans (Equiv.sumCongr e (Equiv.refl _))}
  vertex := N.vertex
  edge := N.edge

variable {K : Type*} [CommSemiring K] {n : ℕ}

theorem singleVertexNetwork_denote (f : Signature K n) : (singleVertexNetwork f).denote=f := by
  funext x
  dsimp [Network.denote,singleVertexNetwork,NetworkShape.assignment]
  simp
  rfl

theorem reorderNetwork_denote (N : Network K n) (e : Equiv.Perm (Fin n)) :
    (reorderNetwork N e).denote=Tensor.reindex e N.denote := by
  funext x
  unfold Network.denote
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext i
  dsimp [NetworkShape.assignment,reorderNetwork]
  cases N.shape.ports ⟨v,i⟩ <;> rfl

end Holant.Certificates.FourthRootOdd
