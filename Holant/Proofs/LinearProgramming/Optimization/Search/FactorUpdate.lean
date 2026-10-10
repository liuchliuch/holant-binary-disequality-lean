import Holant.Proofs.LinearProgramming.Optimization.Search.CapGeometry
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Concrete rational factor-matrix update: center c and factor R describe c+R B₂.
The cut is pulled back by Rᵀ. No inverse or supplied update callback is used.
The determinant theorem is for this very matrix, including the inflation.
Full target containment and rounding of stored matrix entries are not inferred
from a determinant inequality; they are proved separately in Projection,
Containment, and RoundedGeometry.
-/

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.FactorUpdate
open scoped BigOperators Matrix

abbrev Vec (n : ℕ) := Fin n → ℚ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℚ
structure State (n : ℕ) where
  center : Vec n
  factor : Mat n

def square {n : ℕ} (v : Vec n) : ℚ := ∑ j, v j^2
def pulled {n : ℕ} (s : State n) (g : Vec n) : Vec n := s.factor.transpose.mulVec g
def shear {n : ℕ} (v : Vec n) : Mat n :=
  1+Matrix.replicateCol Unit (((Scales.axial n/Scales.transverse n-1)/square v) • v)*
    Matrix.replicateRow Unit v
def transform {n : ℕ} (v : Vec n) : Mat n :=
  (Scales.inflation n*Scales.transverse n) • shear v

/-- Total on all rational inputs; the search must reject zero-normal cuts
before using the nondegenerate correctness theorems. -/
def update {n : ℕ} (s : State n) (g : Vec n) : State n :=
  let v := pulled s g
  let a := NormApprox.value (square v) (Scales.precision n)
  { center := s.center-s.factor.mulVec ((1/(((n:ℚ)+1)*a)) • v)
    factor := s.factor*transform v }

theorem square_nonneg {n : ℕ} (v : Vec n) : 0≤square v :=
  Finset.sum_nonneg (fun j _ => sq_nonneg (v j))

theorem square_pos {n : ℕ} (v : Vec n) (hv : v≠0) : 0<square v := by
  obtain ⟨j,hj⟩ : ∃ j, v j≠0 := by
    by_contra h
    apply hv
    funext j
    simpa using not_exists.mp h j
  have hp : 0<v j^2 := sq_pos_of_ne_zero hj
  have hm : v j^2≤square v := Finset.single_le_sum
    (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j)
  exact hp.trans_le hm

theorem shear_det {n : ℕ} (v : Vec n) (hv : v≠0) :
    (shear v).det=Scales.axial n/Scales.transverse n := by
  have hs := ne_of_gt (square_pos v hv)
  have hd : v ⬝ᵥ (((Scales.axial n/Scales.transverse n-1)/square v) • v)=
      ((Scales.axial n/Scales.transverse n-1)/square v)*square v := by
    change (∑ j, v j*(((Scales.axial n/Scales.transverse n-1)/square v)*v j))=
      ((Scales.axial n/Scales.transverse n-1)/square v)*(∑ j, v j^2)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [shear,Matrix.det_one_add_replicateCol_mul_replicateRow,hd]
  field_simp
  <;> ring

theorem transform_det {n : ℕ} (hn : 2≤n) (v : Vec n) (hv : v≠0) :
    (transform v).det=Scales.inflation n^n*
      (Scales.axial n*Scales.transverse n^(n-1)) := by
  have hb := ne_of_gt (Scales.transverse_pos n)
  rw [transform,Matrix.det_smul,shear_det v hv,Fintype.card_fin,mul_pow]
  have hn' : n=(n-1)+1 := by omega
  have hp : Scales.transverse n^n=Scales.transverse n^(n-1)*Scales.transverse n := by
    calc
      Scales.transverse n^n=Scales.transverse n^((n-1)+1) :=
        congrArg (fun k : ℕ => Scales.transverse n^k) hn'
      _ = _ := pow_succ _ _
  rw [hp]
  field_simp
  <;> ring

theorem transform_det_pos {n : ℕ} (hn : 2≤n) (v : Vec n) (hv : v≠0) :
    0<(transform v).det := by
  rw [transform_det hn v hv]
  exact mul_pos (pow_pos (Scales.inflation_pos n) _)
    (mul_pos (Scales.axial_pos n (by omega)) (pow_pos (Scales.transverse_pos n) _))

theorem transform_contracts {n : ℕ} (hn : 2≤n) (v : Vec n) (hv : v≠0) :
    (transform v).det≤Scales.contraction n := by
  rw [transform_det hn v hv]
  exact Scales.volume_factor n hn

theorem update_det {n : ℕ} (s : State n) (g : Vec n) :
    (update s g).factor.det=s.factor.det*(transform (pulled s g)).det :=
  Matrix.det_mul _ _

theorem update_preserves_nonsingular {n : ℕ} (hn : 2≤n) (s : State n) (g : Vec n)
    (hR : s.factor.det≠0) (hv : pulled s g≠0) : (update s g).factor.det≠0 := by
  rw [update_det]
  exact mul_ne_zero hR (ne_of_gt (transform_det_pos hn _ hv))

theorem update_contracts {n : ℕ} (hn : 2≤n) (s : State n) (g : Vec n)
    (hv : pulled s g≠0) :
    |(update s g).factor.det|≤|s.factor.det| * Scales.contraction n := by
  rw [update_det,abs_mul,abs_of_pos (transform_det_pos hn _ hv)]
  exact mul_le_mul_of_nonneg_left (transform_contracts hn _ hv) (abs_nonneg _)

/-- Scalar one-dimensional branch: exact central interval halving. -/
def intervalUpdate (c r g : ℚ) : ℚ × ℚ :=
  (if 0<g then c-r/2 else c+r/2,r/2)

theorem interval_contains (c r g y : ℚ) (hr : 0≤r) (hg : g≠0)
    (hy : |y-c|≤r) (hcut : g*(y-c)≤0) :
    |y-(intervalUpdate c r g).1|≤(intervalUpdate c r g).2 := by
  obtain ⟨hl,hu⟩ := abs_le.mp hy
  unfold intervalUpdate
  dsimp only
  by_cases hp : 0<g
  · rw [if_pos hp]
    have hside : y-c≤0 := by
      by_contra h
      have := mul_pos hp (lt_of_not_ge h)
      linarith
    apply abs_le.mpr
    constructor <;> linarith
  · rw [if_neg hp]
    have hm : g<0 := lt_of_le_of_ne (le_of_not_gt hp) hg
    have hside : 0≤y-c := by
      by_contra h
      have := mul_pos_of_neg_of_neg hm (lt_of_not_ge h)
      linarith
    apply abs_le.mpr
    constructor <;> linarith


end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.FactorUpdate
