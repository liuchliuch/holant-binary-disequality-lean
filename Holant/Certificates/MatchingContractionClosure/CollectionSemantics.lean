import Holant.Certificates.MatchingContractionClosure.CollectionPorts

namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
variable {P Q E : Type*} [DecidableEq E]

def joinLabels (e : E) (ab : Bool × Bool) (y : OtherEdges e → Bool × Bool) : E → Bool × Bool :=
  fun d => if hd : d=e then ab else y ⟨d,hd⟩

@[simp] theorem joinLabels_self (e : E) (ab : Bool × Bool) (y : OtherEdges e → Bool × Bool) :
    joinLabels e ab y e=ab := by simp [joinLabels]

@[simp] theorem joinLabels_other (e : E) (ab : Bool × Bool) (y : OtherEdges e → Bool × Bool)
    (d : OtherEdges e) : joinLabels e ab y d.val=y d := by simp [joinLabels,d.property]

def splitLabelsEquiv (e : E) : (E → Bool × Bool) ≃ ((Bool × Bool) × (OtherEdges e → Bool × Bool)) where
  toFun y := (y e,fun d => y d.val)
  invFun q := joinLabels e q.1 q.2
  left_inv y := by funext d; by_cases hd : d=e <;> simp [joinLabels,hd]
  right_inv q := by
    apply Prod.ext
    · simp
    · funext d
      simp

variable [DecidableEq P]

theorem collectionAssignment_split (p : CollectionPorts P Q E) (e : E) (x : Q → Bool)
    (a b : Bool) (y : OtherEdges e → Bool × Bool) :
    collectionAssignment p x (joinLabels e (a,b) y)=
      insertPair (p (.inr (e,false))) (p (.inr (e,true))) a b
        (extendRemaining _ _ (collectionAssignment (collectionTailPorts p e) x y)) := by
  funext i
  obtain ⟨s,rfl⟩ := p.surjective i
  rcases s with q | ⟨d,c⟩
  · rw [collectionAssignment_boundary,insertPair_other]
    · change x q=extendRemaining _ _ (collectionAssignment (collectionTailPorts p e) x y)
        (collectionTailPorts p e (.inl q)).val
      rw [extendRemaining_apply,collectionAssignment_boundary]
    · intro he
      cases p.injective he
    · intro he
      cases p.injective he
  · by_cases hd : d=e
    · subst d
      cases c
      · rw [collectionAssignment_edge,joinLabels_self,insertPair_first (collection_pair_distinct p e)]
        simp
      · rw [collectionAssignment_edge,joinLabels_self,insertPair_second]
        simp
    · rw [collectionAssignment_edge,insertPair_other]
      · rw [show joinLabels e (a,b) y d=y ⟨d,hd⟩ from joinLabels_other e (a,b) y ⟨d,hd⟩]
        change (if c then (y ⟨d,hd⟩).2 else (y ⟨d,hd⟩).1)=
          extendRemaining _ _ (collectionAssignment (collectionTailPorts p e) x y)
            (collectionTailPorts p e (.inr (⟨d,hd⟩,c))).val
        rw [extendRemaining_apply,collectionAssignment_edge]
      · intro he
        exact hd (congrArg Prod.fst (Sum.inr.inj (p.injective he)))
      · intro he
        exact hd (congrArg Prod.fst (Sum.inr.inj (p.injective he)))

variable {K : Type*} [Field K] [Fintype E]

def kernelProduct (C : E → Binary (K := K)) (y : E → Bool × Bool) : K :=
  ∏ e, C e (y e).1 (y e).2

theorem kernelProduct_split (C : E → Binary (K := K)) (e : E) (a b : Bool)
    (y : OtherEdges e → Bool × Bool) :
    kernelProduct C (joinLabels e (a,b) y)=C e a b*kernelProduct (fun d => C d.val) y := by
  unfold kernelProduct
  rw [Fintype.prod_eq_mul_prod_compl e,joinLabels_self]
  congr 1
  rw [Finset.prod_subtype (p := fun d : E => d≠e) {e}ᶜ (by intro d; simp)]
  apply Finset.prod_congr rfl
  intro d hd
  rw [joinLabels_other]

/-- Literal simultaneous contraction of any finite disjoint collection on
the original ports. The output type retains precisely its specified boundary. -/
def contractCollection (p : CollectionPorts P Q E) (C : E → Binary (K := K))
    (F : Tensor K P) : Tensor K Q :=
  fun x => ∑ y : E → Bool × Bool, kernelProduct C y*F (collectionAssignment p x y)

/-- Fubini decomposition of the actual complete assignment sum. It is proved
for every tensor, not supplied as a sequence or component certificate. -/
theorem contractCollection_step (p : CollectionPorts P Q E) (C : E → Binary (K := K))
    (F : Tensor K P) (e : E) :
    contractCollection p C F=
      contractCollection (collectionTailPorts p e) (fun d => C d.val)
        (contractPair (p (.inr (e,false))) (p (.inr (e,true))) (C e) F) := by
  funext x
  unfold contractCollection
  rw [← (splitLabelsEquiv e).symm.sum_comp
    (fun y => kernelProduct C y*F (collectionAssignment p x y))]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [Fintype.sum_prod_type,contractPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  change kernelProduct C (joinLabels e (a,b) y)*F (collectionAssignment p x (joinLabels e (a,b) y))=_
  rw [kernelProduct_split,collectionAssignment_split]
  ring

end
end Holant.Certificates.MatchingContractionClosure
