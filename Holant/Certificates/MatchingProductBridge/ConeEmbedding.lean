import Holant.Certificates.MatchingProductBridge.GroupOperations
import Holant.Certificates.MatchingProductBridge.InvertibleBridgeCone

namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matchingTensor_eq_product (r : Fin 3) (U V : Matrix Bool Bool ℂ) :
    matchingTensor r U V = matchingProduct r U V := by
  fin_cases r <;> rfl

/-- Actual source cone factors retain their group direction after scale absorption. -/
theorem matchingCone_presentation (g : PlatonicModel) (W : FourTensor) (h : matchingCone g W) :
    W = 0 ∨ ∃ r : Fin 3, ∃ U V : Matrix Bool Bool ℂ,
      groupDirection g U ∧ groupDirection g V ∧ W = matchingTensor r U V := by
  rcases h with h | ⟨r,U,V,hU,hV,c,hc,he⟩
  · exact Or.inl h
  · have hU' := (groupDirection_right_X_iff g U).mp hU
    have hV' := (groupDirection_right_X_iff g V).mp hV
    refine Or.inr ⟨r,c • Matrix.of U,Matrix.of V,groupDirection_smul g hU' hc,hV',?_⟩
    rw [matchingTensor_smul_left,matchingTensor_eq_product]
    exact he

/-- The literal T/O/I cone embeds in the already proved universal invertible cone. -/
theorem matchingCone_invertible (g : PlatonicModel) (W : FourTensor) (h : matchingCone g W) :
    InvertibleMatchingCone W := by
  rcases matchingCone_presentation g W h with he | ⟨r,U,V,hU,hV,he⟩
  · exact Or.inl he
  · exact Or.inr ⟨r,U,V,groupDirection_det_ne_zero g hU,groupDirection_det_ne_zero g hV,he⟩

/-- Every product of two actual group directions is admitted by the original[UX] deck convention. -/
theorem matchingProduct_mem_cone (g : PlatonicModel) (r : Fin 3) {U V : Binary}
    (hU : groupDirection g U) (hV : groupDirection g V) : matchingCone g (matchingProduct r U V) :=
  Or.inr ⟨r,U,V,groupDirection_right_X g hU,groupDirection_right_X g hV,1,one_ne_zero,by simp⟩

end
end Holant.Certificates.MatchingProductBridge
