import Holant.Certificates.MatchingProductBridge.GroupNonsingularity

/-! Symmetric group directions really admit the source's nonzero real(a,b,d)
coordinates. This follows from the concrete quaternion models and transpose,
not from a supplied coordinate-certificate hypothesis. -/
namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem quaternion_symmetric_iff (v : Fin 4 → ℝ) :
    transpose (quaternion v) = quaternion v ↔ v 2 = 0 := by
  constructor
  · intro h
    have hh := congrFun (congrFun h false) true
    simp [transpose,quaternion,Q0,Q1,Q2,Q3,Holant.Signature.equality] at hh
    have hz : (v 2 : ℂ) = 0 := by linear_combination -(1/2 : ℂ)*hh
    exact Complex.ofReal_eq_zero.mp hz
  · intro hv
    funext a b
    cases a <;> cases b <;> simp [transpose,quaternion,Q0,Q1,Q2,Q3,Holant.Signature.equality,hv]

/-- Real quaternion coordinates exist for every literal projective model member. -/
theorem groupDirection_real_quaternion (g : PlatonicModel) {U : Binary} (h : groupDirection g U) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ U = c • quaternion v := by
  rcases h with ⟨c,hc,V,hV,rfl⟩
  rcases modelBase_quaternion g hV with ⟨v,hv,rfl⟩
  exact ⟨c,hc,v,hv,rfl⟩

/-- This is the actual symmetric representative normalization used in A.15. -/
theorem groupDirection_symmetric_rep (g : PlatonicModel) {U : Binary}
    (h : groupDirection g U) (hs : transpose U = U) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ u : Fin 3 → ℝ, u ≠ 0 ∧ U = c • symmetricQuaternion u := by
  rcases groupDirection_real_quaternion g h with ⟨c,hc,v,hv,rfl⟩
  have hq : transpose (quaternion v) = quaternion v := by
    funext a b
    have hh := congrFun (congrFun hs a) b
    change c * quaternion v b a = c * quaternion v a b at hh
    exact mul_left_cancel₀ hc hh
  have hv2 := (quaternion_symmetric_iff v).mp hq
  let u : Fin 3 → ℝ := ![v 0,v 1,v 3]
  have hu : u ≠ 0 := by
    intro hz
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    have h3 := congrFun hz 2
    apply hv
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact hv2
    · exact h3
  have he : quaternion v = symmetricQuaternion u := by
    funext a b
    simp [quaternion,symmetricQuaternion,u,hv2]
  exact ⟨c,hc,u,hu,by rw [he]⟩

/-- Every binary factor admitted by the source's [UX] convention is nonsingular. -/
theorem matching_factor_det_ne_zero (g : PlatonicModel) {U : Binary}
    (h : groupDirection g (multiply U X)) : Matrix.det (Matrix.of U) ≠ 0 := by
  have hh := groupDirection_det_ne_zero g h
  rw [multiply_eq_matrix_mul,Matrix.det_mul] at hh
  intro hz
  exact hh (by rw [hz,zero_mul])

end
end Holant.Certificates.MatchingProductBridge
