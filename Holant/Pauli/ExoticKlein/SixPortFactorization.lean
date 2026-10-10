import Holant.Pauli.ExoticKlein.SixPortModel
import Holant.Tensor

/-! The matching-product conclusion supplies a literal nontrivial partition
of the original six ports, with both factor tensors nonzero. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators

def splitCoordinates : (Fin 2 ⊕ Fin 4) ≃ (Fin 3 × Bool) :=
  Equiv.ofBijective
    (Sum.elim ![(0,false),(0,true)] ![(1,false),(1,true),(2,false),(2,true)])
    (by decide)

def HasProperTensorFactor (h : Signature ℂ 6) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ ∃ ports : (Fin m ⊕ Fin n) ≃ Fin 6,
    ∃ f : Signature ℂ m, ∃ g : Signature ℂ n,
      f ≠ 0 ∧ g ≠ 0 ∧ h = Tensor.reindex ports (Tensor.tensor f g)

def TensorPrime (h : Signature ℂ 6) : Prop := h ≠ 0 ∧ ¬HasProperTensorFactor h

theorem isProduct_hasProperTensorFactor (h : Signature ℂ 6) (hn : h ≠ 0) (hp : IsProduct h) :
    HasProperTensorFactor h := by
  obtain ⟨M,labels,s,hs,he⟩ := hp
  let ports := splitCoordinates.trans M.ports
  let f : Signature ℂ 2 := fun x => s*E (labels 0) (x 0) (x 1)
  let g : Signature ℂ 4 := fun x => E (labels 1) (x 0) (x 1)*E (labels 2) (x 2) (x 3)
  have hfactors : h = Tensor.reindex ports (Tensor.tensor f g) := by
    rw [he]
    funext x
    simp [Tensor.reindex,Tensor.tensor,ports,splitCoordinates,Equiv.trans_apply,f,g,
      Matching.tensor,Fin.prod_univ_succ]
    ring
  refine ⟨2,4,by decide,by decide,ports,f,g,?_,?_,hfactors⟩
  · intro hz
    apply hn
    rw [hfactors,hz]
    funext x
    simp [Tensor.reindex,Tensor.tensor]
  · intro hz
    apply hn
    rw [hfactors,hz]
    funext x
    simp [Tensor.reindex,Tensor.tensor]

theorem isProduct_not_tensorPrime (h : Signature ℂ 6) (hp : IsProduct h) : ¬TensorPrime h := by
  rintro ⟨hn,hprime⟩
  exact hprime (isProduct_hasProperTensorFactor h hn hp)

end
end Holant.Pauli.ExoticKlein.SixPort
