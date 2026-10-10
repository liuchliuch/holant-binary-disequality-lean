import Holant.Certificates.MatchingProductBridge.TwistedModels

/-! Required operations on the actual Platonic directions: multiplying by the
quaternion axes, transposing, and taking the two-by-two adjugate. -/
namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def axisPermutation1 : Equiv.Perm (Fin 4) where
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv := by decide
  right_inv := by decide

def axisPermutation2 : Equiv.Perm (Fin 4) where
  toFun := ![2,3,0,1]
  invFun := ![2,3,0,1]
  left_inv := by decide
  right_inv := by decide

theorem axisPermutation1_even : Equiv.Perm.sign axisPermutation1 = 1 := by decide
theorem axisPermutation2_even : Equiv.Perm.sign axisPermutation2 = 1 := by decide

def adjugateBinary (U : Binary) : Binary := fun a b =>
  if a = b then U (!a) (!b) else -U a b

theorem groupDirection_coordinate_action (g : PlatonicModel) (F : Binary → Binary)
    (π : Equiv.Perm (Fin 4)) (hπ : Equiv.Perm.sign π = 1) (δ : Fin 4 → Bool)
    (hc : ∀ (c : ℂ) (U : Binary), F (c • U) = c • F U)
    (hq : ∀ v : Fin 4 → ℝ, F (quaternion v) = quaternion (twistVector π δ v))
    {U : Binary} (hU : groupDirection g U) : groupDirection g (F U) := by
  rcases hU with ⟨c,hc0,V,hV,rfl⟩
  rcases modelBase_quaternion g hV with ⟨v,hv,rfl⟩
  rw [hc,hq]
  exact groupDirection_smul g (modelBase_twist_direction g π hπ δ v hV) hc0

theorem multiply_right_Q1_coordinates (v : Fin 4 → ℝ) :
    multiply (quaternion v) Q1 = quaternion (twistVector axisPermutation1 ![true,false,true,false] v) := by
  funext a b
  cases a <;> cases b <;>
    simp [multiply,quaternion,twistVector,axisPermutation1,signBit,Q0,Q1,Q2,Q3,
      Holant.Signature.equality] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem multiply_right_Q2_coordinates (v : Fin 4 → ℝ) :
    multiply (quaternion v) Q2 = quaternion (twistVector axisPermutation2 ![true,false,false,true] v) := by
  funext a b
  cases a <;> cases b <;>
    simp [multiply,quaternion,twistVector,axisPermutation2,signBit,Q0,Q1,Q2,Q3,
      Holant.Signature.equality] <;> ring

theorem adjugate_coordinates (v : Fin 4 → ℝ) :
    adjugateBinary (quaternion v) = quaternion (twistVector (Equiv.refl _) ![false,true,true,true] v) := by
  funext a b
  cases a <;> cases b <;>
    simp [adjugateBinary,quaternion,twistVector,signBit,Q0,Q1,Q2,Q3,Holant.Signature.equality] <;> ring

theorem transpose_coordinates (v : Fin 4 → ℝ) :
    transpose (quaternion v) = quaternion (twistVector (Equiv.refl _) ![false,false,true,false] v) := by
  funext a b
  cases a <;> cases b <;>
    simp [transpose,quaternion,twistVector,signBit,Q0,Q1,Q2,Q3,Holant.Signature.equality] <;> ring

theorem groupDirection_right_Q1 (g : PlatonicModel) {U : Binary} (hU : groupDirection g U) :
    groupDirection g (multiply U Q1) := by
  apply groupDirection_coordinate_action g (fun U => multiply U Q1) axisPermutation1 axisPermutation1_even
    ![true,false,true,false] ?_ multiply_right_Q1_coordinates hU
  intro c U
  funext a b
  simp [multiply,smul_eq_mul]
  ring

theorem groupDirection_right_Q2 (g : PlatonicModel) {U : Binary} (hU : groupDirection g U) :
    groupDirection g (multiply U Q2) := by
  apply groupDirection_coordinate_action g (fun U => multiply U Q2) axisPermutation2 axisPermutation2_even
    ![true,false,false,true] ?_ multiply_right_Q2_coordinates hU
  intro c U
  funext a b
  simp [multiply,smul_eq_mul]
  ring

theorem groupDirection_adjugate (g : PlatonicModel) {U : Binary} (hU : groupDirection g U) :
    groupDirection g (adjugateBinary U) := by
  apply groupDirection_coordinate_action g adjugateBinary (Equiv.refl _) (by simp)
    ![false,true,true,true] ?_ adjugate_coordinates hU
  intro c U
  funext a b
  cases a <;> cases b <;> simp [adjugateBinary,smul_eq_mul]

theorem groupDirection_transpose (g : PlatonicModel) {U : Binary} (hU : groupDirection g U) :
    groupDirection g (transpose U) := by
  apply groupDirection_coordinate_action g transpose (Equiv.refl _) (by simp)
    ![false,false,true,false] ?_ transpose_coordinates hU
  intro c U
  rfl

theorem multiply_right_X_eq (U : Binary) : multiply U X = (-Complex.I) • multiply U Q1 := by
  funext a b
  cases a <;> cases b <;> simp [multiply,X,Q1,Holant.Signature.disequality,smul_eq_mul] <;>
    ring_nf <;> simp [Complex.I_sq]

theorem groupDirection_right_X (g : PlatonicModel) {U : Binary} (hU : groupDirection g U) :
    groupDirection g (multiply U X) := by
  rw [multiply_right_X_eq]
  exact groupDirection_smul g (groupDirection_right_Q1 g hU) (neg_ne_zero.mpr Complex.I_ne_zero)

theorem multiply_X_twice (U : Binary) : multiply (multiply U X) X = U := by
  funext a b
  cases a <;> cases b <;> simp [multiply,X,Holant.Signature.disequality]

theorem groupDirection_right_X_iff (g : PlatonicModel) (U : Binary) :
    groupDirection g (multiply U X) ↔ groupDirection g U := by
  constructor
  · intro h
    simpa only [multiply_X_twice] using groupDirection_right_X g h
  · exact groupDirection_right_X g

end
end Holant.Certificates.MatchingProductBridge
