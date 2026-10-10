import Holant.Platonic.FixedMatchingRuling.SegreTensor
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Exact degree-two interpolation at the twelve projective tetrahedral points.
Zero evaluations are retained; the proof never divides by a test coordinate. -/
namespace Holant.Platonic.FixedMatchingRuling
noncomputable section
open scoped BigOperators

def axis (i : Fin 4) : Fin 4 → ℂ := Pi.single i 1

def signPoint (b : Fin 3 → Bool) : Fin 4 → ℂ :=
  ![1, if b 0 then -1 else 1, if b 1 then -1 else 1, if b 2 then -1 else 1]

def quadratic (c : Fin 10 → ℂ) (x : Fin 4 → ℂ) : ℂ :=
  c 0*x 0^2+c 1*x 1^2+c 2*x 2^2+c 3*x 3^2+
  c 4*x 0*x 1+c 5*x 0*x 2+c 6*x 0*x 3+
  c 7*x 1*x 2+c 8*x 1*x 3+c 9*x 2*x 3

 theorem quadratic_coefficients_zero (c : Fin 10 → ℂ)
    (ha : ∀i, quadratic c (axis i)=0)
    (hs : ∀b, quadratic c (signPoint b)=0) : c=0 := by
  have h0 : c 0=0 := by simpa [quadratic,axis] using ha 0
  have h1 : c 1=0 := by simpa [quadratic,axis] using ha 1
  have h2 : c 2=0 := by simpa [quadratic,axis] using ha 2
  have h3 : c 3=0 := by simpa [quadratic,axis] using ha 3
  have h000 := hs ![false,false,false]
  have h001 := hs ![false,false,true]
  have h010 := hs ![false,true,false]
  have h011 := hs ![false,true,true]
  have h100 := hs ![true,false,false]
  have h101 := hs ![true,false,true]
  have h110 := hs ![true,true,false]
  have h111 := hs ![true,true,true]
  simp [quadratic,signPoint,h0,h1,h2,h3] at h000 h001 h010 h011 h100 h101 h110 h111
  have h4 : c 4=0 := by linear_combination (h000+h001+h010+h011-h100-h101-h110-h111)/8
  have h5 : c 5=0 := by linear_combination (h000+h001-h010-h011+h100+h101-h110-h111)/8
  have h6 : c 6=0 := by linear_combination (h000-h001+h010-h011+h100-h101+h110-h111)/8
  have h7 : c 7=0 := by linear_combination (h000+h001-h010-h011-h100-h101+h110+h111)/8
  have h8 : c 8=0 := by linear_combination (h000-h001+h010-h011-h100+h101-h110+h111)/8
  have h9 : c 9=0 := by linear_combination (h000-h001-h010+h011+h100-h101-h110+h111)/8
  ext i
  fin_cases i <;> simp [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]

 theorem quadratic_vanishes (c : Fin 10 → ℂ)
    (ha : ∀i, quadratic c (axis i)=0)
    (hs : ∀b, quadratic c (signPoint b)=0) (x : Fin 4→ℂ) : quadratic c x=0 := by
  rw [quadratic_coefficients_zero c ha hs]
  simp [quadratic]

 theorem linear_apply_four (L : (Fin 4→ℂ) →ₗ[ℂ] ℂ) (x : Fin 4→ℂ) :
    L x=x 0*L (axis 0)+x 1*L (axis 1)+x 2*L (axis 2)+x 3*L (axis 3) := by
  have hx : x=x 0 • axis 0+x 1 • axis 1+x 2 • axis 2+x 3 • axis 3 := by
    ext i
    fin_cases i <;> simp [axis]
  conv_lhs => rw [hx]
  simp

/-- Coefficients of the pullback of an actual two-by-two flattening minor. -/
def minorCoefficients (A B C D : (Fin 4→ℂ) →ₗ[ℂ] ℂ) : Fin 10→ℂ :=
  ![A (axis 0)*B (axis 0)-C (axis 0)*D (axis 0),
    A (axis 1)*B (axis 1)-C (axis 1)*D (axis 1),
    A (axis 2)*B (axis 2)-C (axis 2)*D (axis 2),
    A (axis 3)*B (axis 3)-C (axis 3)*D (axis 3),
    A (axis 0)*B (axis 1)+A (axis 1)*B (axis 0)-C (axis 0)*D (axis 1)-C (axis 1)*D (axis 0),
    A (axis 0)*B (axis 2)+A (axis 2)*B (axis 0)-C (axis 0)*D (axis 2)-C (axis 2)*D (axis 0),
    A (axis 0)*B (axis 3)+A (axis 3)*B (axis 0)-C (axis 0)*D (axis 3)-C (axis 3)*D (axis 0),
    A (axis 1)*B (axis 2)+A (axis 2)*B (axis 1)-C (axis 1)*D (axis 2)-C (axis 2)*D (axis 1),
    A (axis 1)*B (axis 3)+A (axis 3)*B (axis 1)-C (axis 1)*D (axis 3)-C (axis 3)*D (axis 1),
    A (axis 2)*B (axis 3)+A (axis 3)*B (axis 2)-C (axis 2)*D (axis 3)-C (axis 3)*D (axis 2)]

 theorem minor_polynomial (A B C D : (Fin 4→ℂ) →ₗ[ℂ] ℂ) (x : Fin 4→ℂ) :
    A x*B x-C x*D x=quadratic (minorCoefficients A B C D) x := by
  rw [linear_apply_four A x,linear_apply_four B x,linear_apply_four C x,linear_apply_four D x]
  simp [quadratic,minorCoefficients]
  ring

 theorem minor_vanishes (A B C D : (Fin 4→ℂ) →ₗ[ℂ] ℂ)
    (ha : ∀i,A (axis i)*B (axis i)-C (axis i)*D (axis i)=0)
    (hs : ∀b,A (signPoint b)*B (signPoint b)-C (signPoint b)*D (signPoint b)=0)
    (x : Fin 4→ℂ) : A x*B x-C x*D x=0 := by
  rw [minor_polynomial]
  apply quadratic_vanishes
  · intro i; rw [←minor_polynomial]; exact ha i
  · intro b; rw [←minor_polynomial]; exact hs b

end
end Holant.Platonic.FixedMatchingRuling
