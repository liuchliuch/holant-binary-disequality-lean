import Holant.Certificates.MatchingProductBridge.GroupInverses
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination


namespace Holant.LocalDrafts.TetrahedralCompletion.DeterminantPreservers
open scoped Matrix BigOperators
variable {K : Type*} [Field K]

abbrev Mat (K : Type*) := Matrix Bool Bool K
abbrev Vec (K : Type*) := Bool → K

def matrixUnit (i j : Bool) : Mat K := fun a b => if a=i ∧ b=j then 1 else 0

theorem det_bool (P : Mat K) :
    P.det = P false false*P true true-P false true*P true false := by
  have h := Matrix.det_reindex_self
    Holant.Certificates.MatchingProductBridge.binaryFinEquiv P
  rw [Matrix.det_fin_two] at h
  simpa [Matrix.reindex_apply,
    Holant.Certificates.MatchingProductBridge.binaryFinEquiv] using h.symm

@[simp] theorem det_matrixUnit (i j : Bool) : (matrixUnit (K:=K) i j).det=0 := by
  rw [det_bool]
  cases i <;> cases j <;> simp [matrixUnit]

theorem matrixUnit_ne_zero (i j : Bool) : matrixUnit (K:=K) i j ≠ 0 := by
  intro h
  have he := congrArg (fun M : Mat K => M i j) h
  simpa [matrixUnit] using he

theorem diagonal_units : matrixUnit (K:=K) false false+matrixUnit true true=1 := by
  ext a b
  cases a <;> cases b <;> simp [matrixUnit,Matrix.one_apply]

theorem basis_expansion (X : Mat K) :
    X=X false false • matrixUnit false false+X false true • matrixUnit false true+
      X true false • matrixUnit true false+X true true • matrixUnit true true := by
  ext a b
  cases a <;> cases b <;> simp [matrixUnit]

/-- Actual zero determinant gives every two-column coefficient minor.
This is a direct four-entry calculation, valid also in characteristic two. -/
theorem singular_minor (P : Mat K) (hP : P.det=0) (i j r c : Bool) :
    P i j*P r c=P i c*P r j := by
  rw [det_bool] at hP
  cases i <;> cases j <;> cases r <;> cases c <;>
    first | ring | linear_combination hP | linear_combination -hP

/-- Both vectors of the actual Segre factor are obtained from one original
nonzero entry; no rank-one factor is supplied to this producer. -/
theorem singular_factor (P : Mat K) (hP : P.det=0) (hn : P ≠ 0) :
    ∃ u v : Vec K, u ≠ 0 ∧ v ≠ 0 ∧ P=Matrix.vecMulVec u v := by
  classical
  have hp : ∃ r c : Bool, P r c ≠ 0 := by
    by_contra h
    push_neg at h
    apply hn
    ext r c
    exact h r c
  obtain ⟨r,c,hrc⟩ := hp
  let u : Vec K := fun i => P i c
  let v : Vec K := fun j => P r j/P r c
  refine ⟨u,v,?_,?_,?_⟩
  · intro h
    have he := congrFun h r
    exact hrc he
  · intro h
    have he := congrFun h c
    have : (1 : K)=0 := by simpa [v,hrc] using he
    exact one_ne_zero this
  · ext i j
    change P i j=P i c*(P r j/P r c)
    rw [←mul_div_assoc]
    apply (eq_div_iff hrc).mpr
    exact singular_minor P hP i j r c

def columns (u s : Vec K) : Mat K := fun i j => if j then s i else u i
def rows (v t : Vec K) : Mat K := fun i j => if i then t j else v j

theorem columns_unit_rows (u s v t : Vec K) (b : Bool) :
    columns u s * matrixUnit b b * rows v t =
      if b then Matrix.vecMulVec s t else Matrix.vecMulVec u v := by
  ext i j
  cases b <;> cases i <;> cases j <;>
    simp [columns,rows,matrixUnit,Matrix.mul_apply,Matrix.vecMulVec]

theorem columns_rows (u s v t : Vec K) :
    columns u s * rows v t=Matrix.vecMulVec u v+Matrix.vecMulVec s t := by
  ext i j
  cases i <;> cases j <;>
    simp [columns,rows,Matrix.mul_apply,Matrix.vecMulVec,add_comm]

def diagonalScale (a : K) : Mat K := fun i j =>
  if i=j then (if i then 1 else a) else 0

@[simp] theorem det_diagonalScale (a : K) : (diagonalScale a).det=a := by
  rw [det_bool]
  simp [diagonalScale]

end Holant.LocalDrafts.TetrahedralCompletion.DeterminantPreservers
