import Holant.EightVertex.ProductAnchor.FactorSupport
import Holant.EightVertex.ProductAnchor.MonomialCase
import Holant.EightVertex.ProductAnchor.ProductComponents

/-! Structural clauses of Lemma 4.2, derived from the unrestricted product
predicate and the actual common transformed edge. The dense-case physical
anchor is supplied separately, not hidden in this algebraic classification. -/
namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem common_product_structural_classification (q : Signature Scalar 4)
    (he : EndpointEven q)
    (hP : CommonKPresentationInKCoordinates productClass {⟨4,q⟩}) :
    PureEquality q ∨ TwoWeightedEqualities q ∨ DenseForm q := by
  obtain ⟨_,T,hedge,hfamily⟩ := hP
  have hH : Product (T.symm.action q) := hfamily ⟨4,q⟩ (Set.mem_singleton _)
  have hn : T.symm.action q≠0 := by
    intro hz
    have hh := congrArg T.action hz
    rw [T.action_symm_action] at hh
    have hzero : T.action (0 : Signature Scalar 4)=0 := by
      funext x
      simp [InvertibleKernel.action,Signature.coordinateAction]
    rw [hzero] at hh
    exact he.1 (congrFun hh (fun _ => false))
  rcases product_components (T.symm.action q) hn hH with h | ⟨D,hc,hproper,hD⟩
  · obtain ⟨s,hs⟩ := h
    have hHG := of_complement_support (T.symm.action q) s hs
    have hq : q=Signature.coordinateAction (fun _ => T.matrix)
        (ge4 (T.symm.action q s) (T.symm.action q (complementWord s)) s) := by
      rw [←hHG]
      exact (T.action_symm_action q).symm
    rcases common_product_matrix_forms T hedge with hmon | ⟨a,c,r,ha,hc,hr,hT⟩
    · left
      rw [hq] at he ⊢
      exact monomial_ge_pure _ hmon _ _ s he
    · right; right
      rw [hT] at hq
      rw [hq] at he ⊢
      exact (balanced_ge_dense a c r _ _ ha hc hr s he).2.2
  · right; left
    apply two_weighted_equalities_of_decomposition q he (D.mapAction T.matrix) hc
    · exact fun i => (hproper i).1
    · rw [TensorDecomposition.value_mapAction,hD]
      exact T.action_symm_action q

 theorem common_product_support_card (q : Signature Scalar 4) (he : EndpointEven q)
    (hP : CommonKPresentationInKCoordinates productClass {⟨4,q⟩}) :
    ((Finset.univ : Finset Word4).filter fun x => q x≠0).card=2 ∨
    ((Finset.univ : Finset Word4).filter fun x => q x≠0).card=4 ∨
    ((Finset.univ : Finset Word4).filter fun x => q x≠0).card=8 := by
  rcases common_product_structural_classification q he hP with h | h | h
  · exact Or.inl h.support_card
  · exact Or.inr (Or.inl h.support_card)
  · exact Or.inr (Or.inr h.support_card)

 theorem structural_alternatives_exclusive (q : Signature Scalar 4) :
    ¬(PureEquality q ∧ TwoWeightedEqualities q) ∧
    ¬(PureEquality q ∧ DenseForm q) ∧ ¬(TwoWeightedEqualities q ∧ DenseForm q) := by
  refine ⟨?_,?_,?_⟩ <;> rintro ⟨h,h'⟩ <;>
    have h2 := h.support_card <;> have h3 := h'.support_card <;> omega

end
end Holant.EightVertex.ProductAnchor
