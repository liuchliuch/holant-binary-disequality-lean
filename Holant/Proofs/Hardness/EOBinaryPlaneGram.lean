import Holant.Proofs.Hardness.EOBinaryPlaneCore
import Mathlib.Analysis.Complex.Basic

/-! Exact coefficient algebra for the full-support binary branch. A nonsingular
binary matrix with a nonzero row Gram cross-entry gives an actual strictly
positive, nonsingular real table by Gram contraction and entrywise norm square.
These are formulas; availability as counting oracles is proved separately. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGram
open Holant

def determinant (a b c d : ℂ) : ℂ := a*d-b*c

def cross (a b c d : ℂ) : ℂ := a*star c+b*star d

def leftNorm (a b : ℂ) : ℝ := Complex.normSq a+Complex.normSq b

def table (a b c d : ℂ) : Signature ℝ 2 := fun x=>
  if x 0 then (if x 1 then leftNorm c d ^ 2 else Complex.normSq (cross a b c d))
  else (if x 1 then Complex.normSq (cross a b c d) else leftNorm a b ^ 2)

theorem determinant_identity (a b c d : ℂ) :
    leftNorm a b*leftNorm c d-Complex.normSq (cross a b c d)=
      Complex.normSq (determinant a b c d) := by
  simp only [leftNorm,cross,determinant,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

theorem table_determinant (a b c d : ℂ) :
    table a b c d ![false,false]*table a b c d ![true,true]-
      table a b c d ![false,true]*table a b c d ![true,false]=
      Complex.normSq (determinant a b c d)*
        (leftNorm a b*leftNorm c d+Complex.normSq (cross a b c d)) := by
  change leftNorm a b^2*leftNorm c d^2-Complex.normSq (cross a b c d)*
    Complex.normSq (cross a b c d)=_
  rw [←determinant_identity]
  ring

/-- Every entry is positive and the determinant is strictly positive, so the
resulting real binary is neither a monomial table nor rank one. -/
theorem table_positive_nonsingular (a b c d : ℂ)
    (ha : a≠0) (hc : c≠0) (hd : determinant a b c d≠0) (hx : cross a b c d≠0) :
    (∀z,0<table a b c d z) ∧
      0<table a b c d ![false,false]*table a b c d ![true,true]-
        table a b c d ![false,true]*table a b c d ![true,false] := by
  have hA : 0<leftNorm a b := add_pos_of_pos_of_nonneg
    (Complex.normSq_pos.mpr ha) (Complex.normSq_nonneg b)
  have hC : 0<leftNorm c d := add_pos_of_pos_of_nonneg
    (Complex.normSq_pos.mpr hc) (Complex.normSq_nonneg d)
  have hX : 0<Complex.normSq (cross a b c d) := Complex.normSq_pos.mpr hx
  constructor
  · intro z
    cases h0 : z 0 <;> cases h1 : z 1 <;> simp only [table,h0,h1,ite_true]
    · exact sq_pos_of_pos hA
    · exact hX
    · exact hX
    · exact sq_pos_of_pos hC
  · rw [table_determinant]
    exact mul_pos (Complex.normSq_pos.mpr hd) (add_pos (mul_pos hA hC) hX)

/-- Orthogonal full rows have a nonzero Gram cross-entry after Hadamard square.
No complex order or analytic choice is used. -/
theorem square_cross (a b c d : ℂ) (h : cross a b c d=0) :
    cross (a^2) (b^2) (c^2) (d^2)=2*(a*star c)^2 := by
  have hh : b*star d= -(a*star c) := (eq_neg_iff_add_eq_zero).mpr (by simpa [cross,add_comm] using h)
  simp only [cross,star_pow,←mul_pow,hh,neg_sq]
  ring

theorem square_cross_nonzero (a b c d : ℂ) (ha : a≠0) (hc : c≠0)
    (h : cross a b c d=0) : cross (a^2) (b^2) (c^2) (d^2)≠0 := by
  rw [square_cross a b c d h]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero ha (star_ne_zero.mpr hc)))

theorem square_determinant (a b c d : ℂ) :
    determinant (a^2) (b^2) (c^2) (d^2)=determinant a b c d*(a*d+b*c) := by
  unfold determinant
  ring

/-- The sole obstruction to this two-step Gram route is the explicit signed
cross-product equation ad=-bc. -/
theorem square_route (a b c d : ℂ) (ha : a≠0) (hc : c≠0)
    (hd : determinant a b c d≠0) (hx : cross a b c d=0) (hp : a*d+b*c≠0) :
    (∀z,0<table (a^2) (b^2) (c^2) (d^2) z) ∧
      0<table (a^2) (b^2) (c^2) (d^2) ![false,false]*
        table (a^2) (b^2) (c^2) (d^2) ![true,true]-
        table (a^2) (b^2) (c^2) (d^2) ![false,true]*
        table (a^2) (b^2) (c^2) (d^2) ![true,false] := by
  apply table_positive_nonsingular _ _ _ _ (pow_ne_zero 2 ha) (pow_ne_zero 2 hc)
  · rw [square_determinant]
    exact mul_ne_zero hd hp
  · exact square_cross_nonzero a b c d ha hc hx

/-- Four literal table factors make the symmetric zero-field interaction. -/
def ising (a b c d : ℝ) : Signature ℝ 2 := fun x=>
  if x 0=x 1 then (a*d)^2 else (b*c)^2

theorem ising_parameters (a b c d : ℝ) (ha : 0<a) (hb : 0<b)
    (hc : 0<c) (hd : 0<d) (hdet : a*d≠b*c) :
    0<(a*d)^2 ∧ 0<(b*c)^2 ∧ (a*d)^2≠(b*c)^2 := by
  refine ⟨sq_pos_of_pos (mul_pos ha hd),sq_pos_of_pos (mul_pos hb hc),?_⟩
  intro h
  have hh := (sq_eq_sq_iff_eq_or_eq_neg).mp h
  rcases hh with hh|hh
  · exact hdet hh
  · have hpos := add_pos (mul_pos ha hd) (mul_pos hb hc)
    linarith

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGram
