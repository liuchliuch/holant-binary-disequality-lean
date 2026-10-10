import Holant.Proofs.LinearProgramming.Optimization.Search.FactorUpdate

/-!
Explicit rational preimage for every point in the central half-ball. This
connects the scalar cap calculation to the actual rational factor matrix;
no eigenbasis, feasible point, or update-correctness certificate is an input.
The only approximation here is the computed rational square-root normalizer.
Rounding stored matrix entries is the distinct operation in RoundedGeometry.
-/

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Projection
open FactorUpdate
open scoped BigOperators Matrix

def transversePart {n : ℕ} (v y : Vec n) : Vec n := y-((v ⬝ᵥ y)/square v) • v
def shift {n : ℕ} (v : Vec n) : ℚ :=
  1/(((n:ℚ)+1)*NormApprox.value (square v) (Scales.precision n))
def preimage {n : ℕ} (v y : Vec n) : Vec n :=
  (1/Scales.inflation n) •
    ((1/Scales.transverse n) • transversePart v y+
      (((v ⬝ᵥ y)/square v+shift v)/Scales.axial n) • v)

theorem self_dot {n : ℕ} (v : Vec n) : v ⬝ᵥ v=square v := by
  simp only [dotProduct,square,pow_two]

theorem square_linear {n : ℕ} (x y : Vec n) (a b : ℚ) :
    square (a • x+b • y)=a^2*square x+2*a*b*(x ⬝ᵥ y)+b^2*square y := by
  unfold square
  calc
    _ = ∑ j, (a^2*x j^2+2*a*b*(x j*y j)+b^2*y j^2) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum,dotProduct]

theorem square_smul {n : ℕ} (a : ℚ) (x : Vec n) : square (a • x)=a^2*square x := by
  simpa using square_linear x (0 : Vec n) a 0

theorem perpendicular {n : ℕ} (v y : Vec n) (hv : v≠0) :
    v ⬝ᵥ transversePart v y=0 := by
  have hs := ne_of_gt (square_pos v hv)
  rw [transversePart,dotProduct_sub,dotProduct_smul,self_dot]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem split_square {n : ℕ} (v y : Vec n) (hv : v≠0) :
    square (transversePart v y)+(v ⬝ᵥ y)^2/square v=square y := by
  have hs := ne_of_gt (square_pos v hv)
  have hw : transversePart v y=(1:ℚ) • y+(-((v ⬝ᵥ y)/square v)) • v := by
    ext j
    simp [transversePart,sub_eq_add_neg]
  rw [hw,square_linear,dotProduct_comm y v]
  field_simp
  <;> ring

theorem transform_action {n : ℕ} (v z : Vec n) (hv : v≠0) :
    (transform v).mulVec z = Scales.inflation n •
      (Scales.transverse n • z+
        (((Scales.axial n-Scales.transverse n)/square v)*(v ⬝ᵥ z)) • v) := by
  have hs := ne_of_gt (square_pos v hv)
  have hb := ne_of_gt (Scales.transverse_pos n)
  have ho : (Matrix.replicateCol Unit
      (((Scales.axial n/Scales.transverse n-1)/square v) • v) *
      Matrix.replicateRow Unit v).mulVec z =
      (((Scales.axial n/Scales.transverse n-1)/square v)*(v ⬝ᵥ z)) • v := by
    ext i
    simp only [Matrix.mulVec,Matrix.mul_apply,Matrix.replicateRow,Matrix.replicateCol,
      Matrix.of_apply,Fintype.sum_unique,dotProduct,Pi.smul_apply,smul_eq_mul,
      Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [transform,Matrix.smul_mulVec,shear,Matrix.add_mulVec,Matrix.one_mulVec,ho]
  ext i
  simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  field_simp [hs,hb]

/-- Exact algebraic inverse image, with no matrix inverse operation. -/
theorem preimage_maps {n : ℕ} (hn : 2≤n) (v y : Vec n) (hv : v≠0) :
    (transform v).mulVec (preimage v y)=y+shift v • v := by
  have hs := ne_of_gt (square_pos v hv)
  have ha := ne_of_gt (Scales.axial_pos n (by omega))
  have hb := ne_of_gt (Scales.transverse_pos n)
  have hg := ne_of_gt (Scales.inflation_pos n)
  have hd : v ⬝ᵥ preimage v y=(1/Scales.inflation n)*
      ((((v ⬝ᵥ y)/square v+shift v)/Scales.axial n)*square v) := by
    simp only [preimage,dotProduct_smul,dotProduct_add,perpendicular v y hv,
      self_dot,smul_eq_mul,mul_zero,zero_add]
  rw [transform_action v _ hv,hd]
  ext j
  simp only [preimage,transversePart,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  field_simp
  <;> ring

theorem preimage_square {n : ℕ} (v y : Vec n) (hv : v≠0) :
    square (preimage v y)=
      (square (transversePart v y)/Scales.transverse n^2+
        (((v ⬝ᵥ y)/square v+shift v)/Scales.axial n)^2*square v)/Scales.inflation n^2 := by
  have hperp : transversePart v y ⬝ᵥ v=0 := by
    rw [dotProduct_comm,perpendicular v y hv]
  rw [preimage,square_smul,square_linear,hperp]
  ring

/-- Every rational point of the true half-ball has a rational preimage in
the updated unit ball; the scale error is derived from the actual program.
-/
theorem preimage_in_ball {n : ℕ} (hn : 2≤n) (v y : Vec n) (hv : v≠0)
    (hy : square y≤1) (hcut : v ⬝ᵥ y≤0) : square (preimage v y)≤1 := by
  let r := Real.sqrt (square v:ℝ)
  let t := ((v ⬝ᵥ y : ℚ):ℝ)/r
  let q := (square (transversePart v y):ℝ)
  have hs : (0:ℝ)<(square v:ℝ) := by exact_mod_cast square_pos v hv
  have hr : 0<r := Real.sqrt_pos.mpr hs
  have hr2 : r^2=(square v:ℝ) := Real.sq_sqrt hs.le
  have hq : 0≤q := by
    dsimp only [q]
    exact_mod_cast square_nonneg (transversePart v y)
  have hsplit : q+t^2=(square y:ℝ) := by
    dsimp [q,t]
    rw [div_pow,hr2]
    exact_mod_cast split_square v y hv
  have hball : q+t^2≤1 := by rw [hsplit]; exact_mod_cast hy
  have ht0 : t≤0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hcut) hr.le
  have ht1 : -1≤t := by nlinarith [sq_nonneg (t+1)]
  have hcap := CapGeometry.rounded_cap n hn (square v) (square_pos v hv) t q
    ⟨ht1,ht0⟩ hq hball
  have hR : (NormApprox.value (square v) (Scales.precision n):ℝ)≠0 := by
    exact_mod_cast ne_of_gt (NormApprox.value_pos _ _ (Scales.precision_pos n (by omega)))
  have hN : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hA : (Scales.axial n:ℝ)≠0 := by exact_mod_cast ne_of_gt (Scales.axial_pos n (by omega))
  have hG : (0:ℝ)<(Scales.inflation n:ℝ) := by exact_mod_cast Scales.inflation_pos n
  have he : (square (preimage v y):ℝ)=
      (q/(Scales.transverse n:ℝ)^2+
        (t+Real.sqrt (square v:ℝ)/(((n:ℝ)+1)*
          (NormApprox.value (square v) (Scales.precision n):ℝ)))^2/(Scales.axial n:ℝ)^2)/
        (Scales.inflation n:ℝ)^2 := by
    rw [preimage_square v y hv]
    push_cast
    dsimp [q,t,shift]
    push_cast
    have hrr : Real.sqrt (square v:ℝ)=r := rfl
    rw [hrr]
    field_simp [ne_of_gt hs,ne_of_gt hr,hR,hA]
    simp only [←hr2]
    ring
  have hfinal : (square (preimage v y):ℝ)≤1 := by
    rw [he]
    exact (div_le_one (sq_pos_of_pos hG)).mpr hcap
  exact_mod_cast hfinal

theorem half_ball_covered {n : ℕ} (hn : 2≤n) (v y : Vec n) (hv : v≠0)
    (hy : square y≤1) (hcut : v ⬝ᵥ y≤0) :
    ∃ z : Vec n, square z≤1 ∧ (transform v).mulVec z=y+shift v • v :=
  ⟨preimage v y,preimage_in_ball hn v y hv hy hcut,preimage_maps hn v y hv⟩

end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Projection
