import Holant.Certificates.EqualityQuaternary.MonomialDeck
import Mathlib.Tactic.LinearCombination

/-! The exact C2 Walsh-block calculation in the proof of A.7. Zero
coordinates are retained throughout. This is an algebraic proof clause,
not the still-missing full C2 physical-deck/mixed-sign gadget theorem. -/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2
open Holant.Marked

def SafeBlock (u v x y : Scalar) : Prop :=
  (y + v)^2 = (u + x)^2 ∧ (y - v)^2 = (u - x)^2 ∧
  (x + v)^2 = (u + y)^2 ∧ (x - v)^2 = (u - y)^2

def BlockRelations (u v x y : Scalar) : Prop :=
  v^2 = u^2 ∧ y^2 = x^2 ∧ y*v = u*x ∧ x*v = u*y

theorem safeBlock_iff (u v x y : Scalar) : SafeBlock u v x y ↔ BlockRelations u v x y := by
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    refine ⟨?_,?_,?_,?_⟩
    · linear_combination (h1+h2+h3+h4)/4
    · linear_combination (h1+h2-h3-h4)/4
    · linear_combination (h1-h2)/4
    · linear_combination (h3-h4)/4
  · rintro ⟨h1,h2,h3,h4⟩
    refine ⟨?_,?_,?_,?_⟩
    · linear_combination h1+h2+2*h3
    · linear_combination h1+h2-2*h3
    · linear_combination h1-h2+2*h4
    · linear_combination h1-h2-2*h4

/-- A zero Walsh endpoint forces the other one to vanish, including zero cards. -/
theorem endpoints_zero_iff {u v x y : Scalar} (h : SafeBlock u v x y) : u=0 ↔ v=0 := by
  have he := ((safeBlock_iff u v x y).mp h).1
  constructor <;> intro hz
  · rw [hz,zero_pow (by decide : 2≠0)] at he
    exact sq_eq_zero_iff.mp he
  · rw [hz,zero_pow (by decide : 2≠0)] at he
    exact sq_eq_zero_iff.mp he.symm

theorem active_zero_iff {u v x y : Scalar} (h : SafeBlock u v x y) : x=0 ↔ y=0 := by
  have he := ((safeBlock_iff u v x y).mp h).2.1
  constructor <;> intro hz
  · rw [hz,zero_pow (by decide : 2≠0)] at he
    exact sq_eq_zero_iff.mp he
  · rw [hz,zero_pow (by decide : 2≠0)] at he
    exact sq_eq_zero_iff.mp he.symm

/-- The active-block sign really is its original coefficient quotient. -/
theorem active_sign {u v x y : Scalar} (h : SafeBlock u v x y) (hx : x≠0) :
    y/x=1 ∨ y/x = -1 := by
  have he := ((safeBlock_iff u v x y).mp h).2.1
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp he) with he | he
  · left; simp [he,hx]
  · right; simp [he,hx]

/-- Nonzero Walsh endpoints force one common sign for all three blocks,
including any inactive (zero) blocks. -/
theorem common_sign_of_endpoint (u v : Scalar) (x y : Fin 3 → Scalar)
    (hu : u≠0) (h : ∀ i, SafeBlock u v (x i) (y i)) :
    ∃ eps : Scalar, (eps=1 ∨ eps = -1) ∧ v=eps*u ∧ ∀ i, y i=eps*x i := by
  have hv := ((safeBlock_iff u v (x 0) (y 0)).mp (h 0)).1
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hv with hv | hv
  · refine ⟨1,Or.inl rfl,by simpa using hv,?_⟩
    intro i
    have hi := ((safeBlock_iff u v (x i) (y i)).mp (h i)).2.2.2
    rw [hv] at hi
    have he : u*(y i-x i)=0 := by linear_combination -hi
    simpa using sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hu)
  · refine ⟨-1,Or.inr rfl,by simpa using hv,?_⟩
    intro i
    have hi := ((safeBlock_iff u v (x i) (y i)).mp (h i)).2.2.2
    rw [hv] at hi
    have he : u*(y i+x i)=0 := by linear_combination -hi
    have hz := (mul_eq_zero.mp he).resolve_left hu
    simpa using (eq_neg_iff_add_eq_zero.mpr hz)

/-- The polynomial contradiction at the end of the mixed-sign argument.
Both candidate matching signs are retained; the nonzero x cannot satisfy them. -/
theorem mixed_sign_obstruction (x y z sigma tau : Scalar) (hx : x≠0) (hz : z≠0)
    (hsigma : sigma=1 ∨ sigma = -1) (htau : tau=1 ∨ tau = -1)
    (h1 : y^2+z^2=sigma*x^2) (h2 : x^2+z^2=tau*y^2) (h3 : x^2+y^2=0) : False := by
  rcases hsigma with rfl | rfl <;> rcases htau with rfl | rfl
  · have hx2 : x^2=0 := by linear_combination (h2-h1+2*h3)/4
    exact hx (sq_eq_zero_iff.mp hx2)
  · have hx2 : x^2=0 := by linear_combination (h2-h1)/2
    exact hx (sq_eq_zero_iff.mp hx2)
  · have hz2 : z^2=0 := by linear_combination h1-h3
    exact hz (sq_eq_zero_iff.mp hz2)
  · have hz2 : z^2=0 := by linear_combination h1-h3
    exact hz (sq_eq_zero_iff.mp hz2)

end Holant.Certificates.EqualityQuaternary.C2
