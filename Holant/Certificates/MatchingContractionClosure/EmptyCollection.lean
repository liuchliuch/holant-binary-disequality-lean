import Holant.Certificates.MatchingContractionClosure.CollectionSemantics
import Mathlib.Data.Fintype.Card

namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
variable {K P Q E : Type*} [Field K] [Fintype E] [DecidableEq E]

def emptyBoundary (p : CollectionPorts P Q E) [IsEmpty E] : Q ≃ P :=
  Equiv.ofBijective (fun q => p (.inl q)) (by
    constructor
    · intro q r h
      exact Sum.inl.inj (p.injective h)
    · intro i
      obtain ⟨s,rfl⟩ := p.surjective i
      rcases s with q | ⟨e,b⟩
      · exact ⟨q,rfl⟩
      · exact isEmptyElim e)

@[simp] theorem emptyBoundary_apply (p : CollectionPorts P Q E) [IsEmpty E] (q : Q) :
    emptyBoundary p q=p (.inl q) := rfl

theorem collectionAssignment_empty (p : CollectionPorts P Q E) [IsEmpty E]
    (x : Q → Bool) (y : E → Bool × Bool) :
    collectionAssignment p x y=(fun i => x ((emptyBoundary p).symm i)) := by
  funext i
  obtain ⟨q,rfl⟩ := (emptyBoundary p).surjective i
  rw [Equiv.symm_apply_apply,emptyBoundary_apply,collectionAssignment_boundary]

theorem contractCollection_empty (p : CollectionPorts P Q E) [IsEmpty E]
    (C : E → Binary (K := K)) (F : Tensor K P) :
    contractCollection p C F=Tensor.reindex (emptyBoundary p).symm F := by
  funext x
  simp only [contractCollection,collectionAssignment_empty]
  have hp : ∀ y : E → Bool × Bool, kernelProduct C y=1 := by intro y; simp [kernelProduct]
  simp only [hp,one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_eq_zero,pow_zero,one_nsmul]
  rfl

theorem otherEdges_card_lt (e : E) : Fintype.card (OtherEdges e)<Fintype.card E :=
  Fintype.card_subtype_lt (x := e) (by simp)

theorem contractCollection_zero (p : CollectionPorts P Q E) (C : E → Binary (K := K)) :
    contractCollection p C (0 : Tensor K P)=0 := by
  funext x
  simp [contractCollection]

end
end Holant.Certificates.MatchingContractionClosure
