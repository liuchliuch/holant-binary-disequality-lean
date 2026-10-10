import Holant.Certificates.MatchingProductBridge.Polarization
import Holant.Certificates.MatchingProductBridge.OrthogonalProjectors
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def dot (u v : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, u i*v i

def vectorNorm (u : Fin 3 → ℝ) : ℝ := Real.sqrt (normSquare u)
def normalizeVector (u : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => u i / vectorNorm u

theorem vectorNorm_pos (u : Fin 3 → ℝ) (hu : u ≠ 0) : 0 < vectorNorm u :=
  Real.sqrt_pos.mpr (normSquare_pos u hu)

theorem vectorNorm_sq (u : Fin 3 → ℝ) : (vectorNorm u)^2 = normSquare u := by
  apply Real.sq_sqrt
  unfold normSquare
  positivity

theorem normalizeVector_dot (u v : Fin 3 → ℝ) :
    dot (normalizeVector u) (normalizeVector v) = dot u v / (vectorNorm u * vectorNorm v) := by
  simp only [dot,normalizeVector,div_eq_mul_inv,Finset.sum_mul,mul_inv_rev]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_self (u : Fin 3 → ℝ) : dot u u = normSquare u := by
  simp [dot,Fin.sum_univ_succ,normSquare,pow_two,add_assoc]

theorem normalizeVector_unit (u : Fin 3 → ℝ) (hu : u ≠ 0) : dot (normalizeVector u) (normalizeVector u) = 1 := by
  rw [normalizeVector_dot,dot_self,← pow_two,vectorNorm_sq]
  exact div_self (ne_of_gt (normSquare_pos u hu))

def realProjectorMatrix (u : Fin 3 → ℝ) : RealFrame := fun i j => u i*u j/normSquare u

theorem normalizeVector_outer (u : Fin 3 → ℝ) (i j : Fin 3) :
    normalizeVector u i * normalizeVector u j = realProjectorMatrix u i j := by
  simp only [normalizeVector,div_mul_div_comm,← pow_two,vectorNorm_sq,realProjectorMatrix]

def realFrame (u v w : Fin 3 → ℝ) : RealFrame :=
  fun i j => ![normalizeVector u i,normalizeVector v i,normalizeVector w i] j

theorem realFrame_unit (u v w : Fin 3 → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    UnitColumns (realFrame u v w) := by
  intro j
  fin_cases j
  · exact normalizeVector_unit u hu
  · exact normalizeVector_unit v hv
  · exact normalizeVector_unit w hw

theorem realFrame_projectors (u v w : Fin 3 → ℝ) :
    (∑ k : Fin 3, columnProjector (realFrame u v w) k) =
      realProjectorMatrix u + realProjectorMatrix v + realProjectorMatrix w := by
  ext i j
  simp only [Matrix.sum_apply,Fin.sum_univ_succ,columnProjector,Matrix.vecMulVec_apply,realFrame]
  change normalizeVector u i*normalizeVector u j+
    (normalizeVector v i*normalizeVector v j+(normalizeVector w i*normalizeVector w j+0)) = _
  rw [normalizeVector_outer,normalizeVector_outer,normalizeVector_outer]
  simp [add_assoc]

def complexify (M : RealFrame) : CoefficientMatrix := fun i j => (M i j : ℂ)

theorem complexify_one_iff (M : RealFrame) : complexify M = 1 ↔ M = 1 := by
  constructor
  · intro h
    ext i j
    have he := congrArg Complex.re (congrFun (congrFun h i) j)
    by_cases hij : i = j <;> simpa [complexify,Matrix.one_apply,hij] using he
  · rintro rfl
    ext i j
    by_cases hij : i = j <;> simp [complexify,Matrix.one_apply,hij]

theorem complexify_projectors (u v w : Fin 3 → ℝ) :
    complexify (realProjectorMatrix u + realProjectorMatrix v + realProjectorMatrix w) =
      realProjector u + realProjector v + realProjector w := by
  ext i j
  simp [complexify,realProjectorMatrix,realProjector]

theorem realFrame_orthogonal_iff (u v w : Fin 3 → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    OrthogonalColumns (realFrame u v w) ↔ dot u v = 0 ∧ dot u w = 0 ∧ dot v w = 0 := by
  have hnu := ne_of_gt (vectorNorm_pos u hu)
  have hnv := ne_of_gt (vectorNorm_pos v hv)
  have hnw := ne_of_gt (vectorNorm_pos w hw)
  constructor
  · intro h
    have h01 := h 0 1 (by decide)
    have h02 := h 0 2 (by decide)
    have h12 := h 1 2 (by decide)
    change dot (normalizeVector u) (normalizeVector v) = 0 at h01
    change dot (normalizeVector u) (normalizeVector w) = 0 at h02
    change dot (normalizeVector v) (normalizeVector w) = 0 at h12
    rw [normalizeVector_dot] at h01 h02 h12
    simpa [div_eq_zero_iff,hnu,hnv,hnw] using And.intro h01 (And.intro h02 h12)
  · rintro ⟨h01,h02,h12⟩
    have h01' : dot (normalizeVector u) (normalizeVector v) = 0 := by rw [normalizeVector_dot,h01]; simp
    have h02' : dot (normalizeVector u) (normalizeVector w) = 0 := by rw [normalizeVector_dot,h02]; simp
    have h12' : dot (normalizeVector v) (normalizeVector w) = 0 := by rw [normalizeVector_dot,h12]; simp
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | simpa [realFrame,dot,Fin.sum_univ_succ,mul_comm] using h01'
      | simpa [realFrame,dot,Fin.sum_univ_succ,mul_comm] using h02'
      | simpa [realFrame,dot,Fin.sum_univ_succ,mul_comm] using h12'

/-- The full nonexceptional orthogonal-triple assertion of Lemma A.15. -/
theorem R_triple_sum_iff_orthogonal (u v w : Fin 3 → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    R u + R v + R w = (fun x => (A x+B x)/2) ↔
      dot u v = 0 ∧ dot u w = 0 ∧ dot v w = 0 := by
  rw [R_sum_iff_projector_sum,← complexify_projectors,complexify_one_iff,← realFrame_projectors]
  exact (projector_sum_identity_iff _ (realFrame_unit u v w hu hv hw)).trans
    (realFrame_orthogonal_iff u v w hu hv hw)

end
end Holant.Certificates.MatchingProductBridge
