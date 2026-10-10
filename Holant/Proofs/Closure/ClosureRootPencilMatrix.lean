import Holant.Kernel
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! Exact two-by-two rulings for a linear matrix family through an actual
rank-one anchor. The ruling is derived from the coordinate determinant
equations. No common factorization, support pattern, or desired ruling is an
input. This algebraic helper does not itself synthesize a physical gadget. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil.Matrix
open Holant

/-- The actual ordered two-by-two determinant coordinate equation. -/
def det2 (M : Kernel ℂ) : ℂ :=
  M false false * M true true - M false true * M true false

/-- Exact factor a, with the varying factor recovered from the literal first row. -/
def FixedLeft (a : Bool → ℂ) (M : Kernel ℂ) : Prop :=
  ∀ i j, M i j = a i * (M false j / a false)

/-- Exact factor b, with the varying factor recovered from the literal first column. -/
def FixedRight (b : Bool → ℂ) (M : Kernel ℂ) : Prop :=
  ∀ i j, M i j = (M i false / b false) * b j

private theorem fixedLeft_of_cross (a : Bool → ℂ) (M : Kernel ℂ)
    (ha : a false ≠ 0)
    (cross : ∀ j, a false * M true j = a true * M false j) : FixedLeft a M := by
  intro i j
  cases i
  · exact (mul_div_cancel₀ (M false j) ha).symm
  · apply mul_left_cancel₀ ha
    calc
      a false * M true j = a true * M false j := cross j
      _ = a true * (a false * (M false j / a false)) := by
        rw [mul_div_cancel₀ _ ha]
      _ = a false * (a true * (M false j / a false)) := (mul_left_comm _ _ _).symm

private theorem fixedRight_of_cross (b : Bool → ℂ) (M : Kernel ℂ)
    (hb : b false ≠ 0)
    (cross : ∀ i, b false * M i true = b true * M i false) : FixedRight b M := by
  intro i j
  cases j
  · exact (div_mul_cancel₀ (M i false) hb).symm
  · apply mul_right_cancel₀ hb
    calc
      M i true * b false = b true * M i false := by
        simpa only [mul_comm] using cross i
      _ = ((M i false / b false) * b true) * b false := by
        rw [mul_right_comm (M i false / b false) (b true) (b false), div_mul_cancel₀ _ hb]
        exact mul_comm _ _

/-- Polarizing the determinant at the actual anchor and the direction
derives one of the two exact fixed factors for that direction. -/
theorem direction_ruling (V : Kernel ℂ) (a b : Bool → ℂ)
    (ha : a false ≠ 0) (hb : b false ≠ 0)
    (directionMinor : det2 V = 0)
    (anchorDirectionMinor : det2 (fun i j => a i * b j + V i j) = 0) :
    FixedLeft a V ∨ FixedRight b V := by
  have tangent : a false * b false * V true true + a true * b true * V false false -
      a false * b true * V true false - a true * b false * V false true = 0 := by
    dsimp only [det2] at directionMinor anchorDirectionMinor
    linear_combination anchorDirectionMinor - directionMinor
  have alternatives :
      (a false * V true false - a true * V false false) *
        (b false * V false true - b true * V false false) = 0 := by
    dsimp only [det2] at directionMinor
    linear_combination (-a false * b false) * directionMinor + V false false * tangent
  rcases mul_eq_zero.mp alternatives with left | right
  · have otherProduct : b false * (a false * V true true - a true * V false true) = 0 := by
      linear_combination tangent + b true * left
    have other : a false * V true true - a true * V false true = 0 :=
      (mul_eq_zero.mp otherProduct).resolve_left hb
    left
    apply fixedLeft_of_cross a V ha
    intro j
    cases j
    · exact sub_eq_zero.mp left
    · exact sub_eq_zero.mp other
  · have otherProduct : a false * (b false * V true true - b true * V true false) = 0 := by
      linear_combination tangent + a true * right
    have other : b false * V true true - b true * V true false = 0 :=
      (mul_eq_zero.mp otherProduct).resolve_left ha
    right
    apply fixedRight_of_cross b V hb
    intro i
    cases i
    · exact sub_eq_zero.mp right
    · exact sub_eq_zero.mp other

/-- The fixed side is common to both U and V, and hence to their entire
linear span. Every anchor entry is genuinely nonzero by the explicit inputs.
The only algebraic premise is the determinant equation on all combinations. -/
theorem linear_ruling (U V : Kernel ℂ) (t0 : ℂ) (a b : Bool → ℂ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (anchor : U + t0 • V = fun i j => a i * b j)
    (minors : ∀ s t : ℂ, det2 (s • U + t • V) = 0) :
    (FixedLeft a U ∧ FixedLeft a V) ∨ (FixedRight b U ∧ FixedRight b V) := by
  have entries (i j : Bool) : U i j + t0 * V i j = a i * b j := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun (congrFun anchor i) j
  have directionMinor : det2 V = 0 := by
    have identity : (0 : ℂ) • U+(1 : ℂ) • V=V := by
      funext i j
      change (0 : ℂ)*U i j+1*V i j=V i j
      ring
    simpa only [identity] using minors 0 1
  have anchorDirectionMinor : det2 (fun i j => a i * b j + V i j) = 0 := by
    have same : (1 : ℂ) • U + (t0 + 1) • V = fun i j => a i * b j + V i j := by
      funext i j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      calc
        U i j + (t0 + 1) * V i j = (U i j + t0 * V i j) + V i j := by ring
        _ = a i * b j + V i j := congrArg (fun z => z + V i j) (entries i j)
    rw [← same]
    exact minors 1 (t0 + 1)
  rcases direction_ruling V a b (ha false) (hb false) directionMinor anchorDirectionMinor with
    left | right
  · have crossV : ∀ j, a false * V true j = a true * V false j := by
      intro j
      rw [left true j]
      calc
        a false * (a true * (V false j / a false)) =
            a true * (a false * (V false j / a false)) := mul_left_comm _ _ _
        _ = a true * V false j := by rw [mul_div_cancel₀ _ (ha false)]
    have crossU : ∀ j, a false * U true j = a true * U false j := by
      intro j
      linear_combination a false * (entries true j) - a true * (entries false j) - t0 * (crossV j)
    exact Or.inl ⟨fixedLeft_of_cross a U (ha false) crossU, left⟩
  · have crossV : ∀ i, b false * V i true = b true * V i false := by
      intro i
      rw [right i true]
      calc
        b false * ((V i false / b false) * b true) =
            ((V i false / b false) * b false) * b true := by ring
        _ = V i false * b true := by rw [div_mul_cancel₀ _ (hb false)]
        _ = b true * V i false := mul_comm _ _
    have crossU : ∀ i, b false * U i true = b true * U i false := by
      intro i
      linear_combination b false * (entries i true) - b true * (entries i false) - t0 * (crossV i)
    exact Or.inr ⟨fixedRight_of_cross b U (hb false) crossU, right⟩

/-- Fully expanded coordinate boundary, suitable for internally derived
root-pencil minor equations. Both exact factorization identities are outputs. -/
theorem coordinate_linear_ruling (U V : Kernel ℂ) (t0 : ℂ) (a b : Bool → ℂ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (anchor : U + t0 • V = fun i j => a i * b j)
    (minors : ∀ s t : ℂ,
      (s * U false false + t * V false false) * (s * U true true + t * V true true) -
        (s * U false true + t * V false true) * (s * U true false + t * V true false) = 0) :
    ((∀ i j, U i j = a i * (U false j / a false)) ∧
      (∀ i j, V i j = a i * (V false j / a false))) ∨
    ((∀ i j, U i j = (U i false / b false) * b j) ∧
      (∀ i j, V i j = (V i false / b false) * b j)) := by
  apply linear_ruling U V t0 a b ha hb anchor
  intro s t
  simpa only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using minors s t

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil.Matrix
