import Holant.Certificates.TetrahedralPreservers.ExternalCoordinates

/-! Exact equivalence of the source's two-sided conditions under its literal
external similarity, including preservation of actual linear-map rank. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

theorem oneSided_transport {S E : Set V} {T B A : End}
    (hT : ∀ r ∈ S, T *ᵥ r ∈ E) (hB : ∀ r ∈ E, B *ᵥ r ∈ S)
    (hA : OneSided S A) : OneSided E (T*A*B) := by
  intro r hr
  simp only [← Matrix.mulVec_mulVec]
  rcases hA _ (hB r hr) with h | h
  · simp [h]
  · exact Or.inr (hT _ h)

theorem conjugation_cancel (T B A : End) (hBT : B*T=1) : B*(T*A*B)*T=A := by
  calc
    B*(T*A*B)*T = (B*T)*A*(B*T) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hBT]; simp

theorem oneSided_transport_iff {S E : Set V} (T B A : End) (hBT : B*T=1)
    (hT : ∀ r ∈ S, T *ᵥ r ∈ E) (hB : ∀ r ∈ E, B *ᵥ r ∈ S) :
    OneSided E (T*A*B) ↔ OneSided S A := by
  constructor
  · intro h
    have hh := oneSided_transport hB hT h
    simpa only [conjugation_cancel T B A hBT] using hh
  · exact oneSided_transport hT hB

def toExternal (A : End) : End := theta*A*thetaInv
def toStandard (A : End) : End := thetaInv*A*theta

@[simp] theorem toStandard_toExternal (A : End) : toStandard (toExternal A)=A :=
  conjugation_cancel theta thetaInv A theta_inverses.2

@[simp] theorem toExternal_toStandard (A : End) : toExternal (toStandard A)=A :=
  conjugation_cancel thetaInv theta A theta_inverses.1

theorem sharp_toExternal (A : End) : sharp (toExternal A) = thetaInv * sharp A * theta := by
  simp [toExternal,sharp_mul,Matrix.mul_assoc]

/-- Both directions of Proposition 9.27's transport, for every complex map. -/
theorem external_twoSided_iff (A : End) :
    TwoSided External (toExternal A) ↔ TwoSided Standard A := by
  constructor
  · intro h
    constructor
    · exact (oneSided_transport_iff theta thetaInv A theta_inverses.2
        (fun _ => theta_standard_external) (fun _ => thetaInv_external_standard)).mp h.1
    · have hh := h.2
      rw [sharp_toExternal] at hh
      exact (oneSided_transport_iff thetaInv theta (sharp A) theta_inverses.1
        (fun _ => thetaInv_standard_external) (fun _ => theta_external_standard)).mp hh
  · intro h
    constructor
    · exact oneSided_transport (fun _ => theta_standard_external)
        (fun _ => thetaInv_external_standard) h.1
    · rw [sharp_toExternal]
      exact oneSided_transport (fun _ => thetaInv_standard_external)
        (fun _ => theta_external_standard) h.2

theorem standard_twoSided_iff (A : End) :
    TwoSided Standard (toStandard A) ↔ TwoSided External A := by
  simpa only [toExternal_toStandard] using (external_twoSided_iff (toStandard A)).symm

theorem theta_det_ne_zero : theta.det ≠ 0 := by
  have h := congrArg Matrix.det theta_inverses.1
  simp only [Matrix.det_mul,Matrix.det_one] at h
  intro hn
  simp [hn] at h

theorem thetaInv_det_ne_zero : thetaInv.det ≠ 0 := by
  have h := congrArg Matrix.det theta_inverses.2
  simp only [Matrix.det_mul,Matrix.det_one] at h
  intro hn
  simp [hn] at h

@[simp] theorem rank_toExternal (A : End) : (toExternal A).rank = A.rank := by
  rw [toExternal,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ thetaInv_det_ne_zero,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ theta_det_ne_zero]

@[simp] theorem rank_toStandard (A : End) : (toStandard A).rank = A.rank := by
  rw [toStandard,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ theta_det_ne_zero,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ thetaInv_det_ne_zero]

/-- A bijection of the actual preserver loci, with the matrix rank retained. -/
def externalPreserverEquiv : {A : End // TwoSided Standard A} ≃
    {A : End // TwoSided External A} where
  toFun A := ⟨toExternal A,(external_twoSided_iff A).mpr A.property⟩
  invFun A := ⟨toStandard A,(standard_twoSided_iff A).mpr A.property⟩
  left_inv A := Subtype.ext (toStandard_toExternal A)
  right_inv A := Subtype.ext (toExternal_toStandard A)

end Holant.Certificates.TetrahedralPreservers
