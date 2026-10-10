import Holant.ReedMuller.FlatNetwork.Collection

/-! The named-port contraction sum is exactly the full half-edge assignment
sum filtered by the ordered boundary. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P Q E : Type*} [Fintype P] [Fintype Q] [Fintype E] [DecidableEq P] [DecidableEq E]

def collectionFullAssignments (p : CollectionPorts P Q E) :
    (P → Bool) ≃ ((Q → Bool) × (E → Bool × Bool)) where
  toFun z := (fun q => z (p (.inl q)),fun e => (z (p (.inr (e,false))),z (p (.inr (e,true)))))
  invFun q := collectionAssignment p q.1 q.2
  left_inv z := by
    funext i
    change collectionAssignment p (fun q => z (p (.inl q)))
      (fun e => (z (p (.inr (e,false))),z (p (.inr (e,true))))) i=z i
    obtain ⟨q,rfl⟩ := p.surjective i
    rcases q with q | ⟨e,b⟩
    · rw [collectionAssignment_boundary]
    · rw [collectionAssignment_edge];cases b <;> rfl
  right_inv q := by
    apply Prod.ext
    · funext i;exact collectionAssignment_boundary p q.1 q.2 i
    · funext e;apply Prod.ext <;> simp only [collectionAssignment_edge,Bool.false_eq_true,ite_false,ite_true]

theorem contractCollection_filtered (p : CollectionPorts P Q E) (C : E → Binary (K := ℂ))
    (F : Tensor ℂ P) (x : Q → Bool) :
    contractCollection p C F x=
      ∑ z : P → Bool,if (∀ q,z (p (.inl q))=x q) then
        (∏ e,C e (z (p (.inr (e,false)))) (z (p (.inr (e,true)))))*F z else 0 := by
  rw [←(collectionFullAssignments p).symm.sum_comp,Fintype.sum_prod_type]
  have hb (a : Q → Bool) (b : E → Bool × Bool) :
      (∀ q,(collectionFullAssignments p).symm (a,b) (p (.inl q))=x q) ↔ a=x := by
    simp only [collectionFullAssignments,Equiv.coe_fn_symm_mk,collectionAssignment_boundary,funext_iff]
  simp only [hb]
  symm
  rw [Finset.sum_eq_single x]
  · apply Finset.sum_congr rfl
    intro y _
    simp only [ite_true]
    change (∏ e,C e (collectionAssignment p x y (p (.inr (e,false))))
      (collectionAssignment p x y (p (.inr (e,true)))))*F (collectionAssignment p x y)=_
    simp only [collectionAssignment_edge,Bool.false_eq_true,ite_false,ite_true]
    rfl
  · intro a _ ha
    simp [ha]
  · simp

end
end Holant.ReedMuller.FlatNetwork
