import Holant.Certificates.OctahedralSeparator.OutputData

namespace Holant.Certificates.OctahedralSeparator
open Holant
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def outsideDirection : Fin 48 → Fin 4 → ℤ := ![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0],![1,-1,1,0],![1,-1,0,-1],![1,-3,1,-1],![1,-3,-1,1],![1,-3,1,1],![1,-3,-1,-1],![1,-1,0,-1],![1,-3,1,-1],![1,-3,-1,-1],![1,-3,1,-1],![1,-1,0,-1],![1,-3,-1,-1],![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,2,-1,1],![0,2,-1,-1],![1,2,0,1],![1,-2,0,-1],![1,2,-1,0],![1,-2,1,0],![0,2,1,1],![1,2,0,1],![1,2,1,0],![1,2,0,1],![0,2,1,1],![1,2,1,0]]
def directionMatrix (j : Fin 48) : Mat := fun a b => ∑ μ : Fin 4, rat (outsideDirection j μ)*(q μ a b)
def outsideScale : Fin 48 → Scalar := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(coeff 0 0 (3/8) (1/4)),(coeff 0 0 (3/8) (1/4)),(coeff 0 0 (3/32) (1/16)),(coeff 0 0 (3/32) (1/16)),(coeff 0 0 (3/32) (1/16)),(coeff 0 0 (3/32) (1/16)),(coeff 0 0 (3/16) (1/8)),(coeff 0 0 (3/32) (1/16)),(coeff 0 0 (3/32) (1/16)),(coeff 0 0 (3/32) (1/16)),(coeff 0 0 (3/16) (1/8)),(coeff 0 0 (3/32) (1/16)),0,0,0,(coeff 0 0 (-1/8) (-3/32)),(coeff 0 0 (-1/8) (-3/32)),(coeff 0 0 (-1/4) (-3/16)),(coeff 0 0 (1/4) (3/16)),(coeff 0 0 (-1/8) (-3/32)),(coeff 0 0 (1/8) (3/32)),(coeff 0 0 (1/8) (3/32)),(coeff 0 0 (1/8) (3/32)),(coeff 0 0 (1/8) (3/32)),(coeff 0 0 (1/8) (3/32)),(coeff 0 0 (1/8) (3/32)),(coeff 0 0 (1/8) (3/32))]
def outsideDeterminant (j : Fin 48) : Scalar := if ((rowForm j)=2 ∧ ((rowBase j)=3 ∨ (rowBase j)=4)) ∨ ((rowForm j)=3 ∧ ((rowBase j)=5 ∨ (rowBase j)=6)) then coeff (51/64) (36/64) 0 0 else coeff (51/256) (36/256) 0 0
theorem outside_direction_21 : pull (rowForm 21) (mm (outsideValues 21) flip)=ms (outsideScale 21) (directionMatrix 21) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_21 : determinant (outsideValues 21)=outsideDeterminant 21 := by decide +kernel
theorem outside_direction_22 : pull (rowForm 22) (mm (outsideValues 22) flip)=ms (outsideScale 22) (directionMatrix 22) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_22 : determinant (outsideValues 22)=outsideDeterminant 22 := by decide +kernel
theorem outside_direction_23 : pull (rowForm 23) (mm (outsideValues 23) flip)=ms (outsideScale 23) (directionMatrix 23) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_23 : determinant (outsideValues 23)=outsideDeterminant 23 := by decide +kernel
theorem outside_direction_24 : pull (rowForm 24) (mm (outsideValues 24) flip)=ms (outsideScale 24) (directionMatrix 24) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_24 : determinant (outsideValues 24)=outsideDeterminant 24 := by decide +kernel
theorem outside_direction_25 : pull (rowForm 25) (mm (outsideValues 25) flip)=ms (outsideScale 25) (directionMatrix 25) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_25 : determinant (outsideValues 25)=outsideDeterminant 25 := by decide +kernel
theorem outside_direction_26 : pull (rowForm 26) (mm (outsideValues 26) flip)=ms (outsideScale 26) (directionMatrix 26) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_26 : determinant (outsideValues 26)=outsideDeterminant 26 := by decide +kernel
theorem outside_direction_27 : pull (rowForm 27) (mm (outsideValues 27) flip)=ms (outsideScale 27) (directionMatrix 27) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_27 : determinant (outsideValues 27)=outsideDeterminant 27 := by decide +kernel
theorem outside_direction_28 : pull (rowForm 28) (mm (outsideValues 28) flip)=ms (outsideScale 28) (directionMatrix 28) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_28 : determinant (outsideValues 28)=outsideDeterminant 28 := by decide +kernel
theorem outside_direction_29 : pull (rowForm 29) (mm (outsideValues 29) flip)=ms (outsideScale 29) (directionMatrix 29) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_29 : determinant (outsideValues 29)=outsideDeterminant 29 := by decide +kernel
theorem outside_direction_30 : pull (rowForm 30) (mm (outsideValues 30) flip)=ms (outsideScale 30) (directionMatrix 30) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_30 : determinant (outsideValues 30)=outsideDeterminant 30 := by decide +kernel
theorem outside_direction_31 : pull (rowForm 31) (mm (outsideValues 31) flip)=ms (outsideScale 31) (directionMatrix 31) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_31 : determinant (outsideValues 31)=outsideDeterminant 31 := by decide +kernel
theorem outside_direction_32 : pull (rowForm 32) (mm (outsideValues 32) flip)=ms (outsideScale 32) (directionMatrix 32) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_32 : determinant (outsideValues 32)=outsideDeterminant 32 := by decide +kernel
theorem outside_direction_36 : pull (rowForm 36) (mm (outsideValues 36) flip)=ms (outsideScale 36) (directionMatrix 36) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_36 : determinant (outsideValues 36)=outsideDeterminant 36 := by decide +kernel
theorem outside_direction_37 : pull (rowForm 37) (mm (outsideValues 37) flip)=ms (outsideScale 37) (directionMatrix 37) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_37 : determinant (outsideValues 37)=outsideDeterminant 37 := by decide +kernel
theorem outside_direction_38 : pull (rowForm 38) (mm (outsideValues 38) flip)=ms (outsideScale 38) (directionMatrix 38) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_38 : determinant (outsideValues 38)=outsideDeterminant 38 := by decide +kernel
theorem outside_direction_39 : pull (rowForm 39) (mm (outsideValues 39) flip)=ms (outsideScale 39) (directionMatrix 39) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_39 : determinant (outsideValues 39)=outsideDeterminant 39 := by decide +kernel
theorem outside_direction_40 : pull (rowForm 40) (mm (outsideValues 40) flip)=ms (outsideScale 40) (directionMatrix 40) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_40 : determinant (outsideValues 40)=outsideDeterminant 40 := by decide +kernel
theorem outside_direction_41 : pull (rowForm 41) (mm (outsideValues 41) flip)=ms (outsideScale 41) (directionMatrix 41) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_41 : determinant (outsideValues 41)=outsideDeterminant 41 := by decide +kernel
theorem outside_direction_42 : pull (rowForm 42) (mm (outsideValues 42) flip)=ms (outsideScale 42) (directionMatrix 42) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_42 : determinant (outsideValues 42)=outsideDeterminant 42 := by decide +kernel
theorem outside_direction_43 : pull (rowForm 43) (mm (outsideValues 43) flip)=ms (outsideScale 43) (directionMatrix 43) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_43 : determinant (outsideValues 43)=outsideDeterminant 43 := by decide +kernel
theorem outside_direction_44 : pull (rowForm 44) (mm (outsideValues 44) flip)=ms (outsideScale 44) (directionMatrix 44) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_44 : determinant (outsideValues 44)=outsideDeterminant 44 := by decide +kernel
theorem outside_direction_45 : pull (rowForm 45) (mm (outsideValues 45) flip)=ms (outsideScale 45) (directionMatrix 45) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_45 : determinant (outsideValues 45)=outsideDeterminant 45 := by decide +kernel
theorem outside_direction_46 : pull (rowForm 46) (mm (outsideValues 46) flip)=ms (outsideScale 46) (directionMatrix 46) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_46 : determinant (outsideValues 46)=outsideDeterminant 46 := by decide +kernel
theorem outside_direction_47 : pull (rowForm 47) (mm (outsideValues 47) flip)=ms (outsideScale 47) (directionMatrix 47) := by
  funext a b
  cases a <;> cases b <;> decide +kernel
theorem outside_determinant_47 : determinant (outsideValues 47)=outsideDeterminant 47 := by decide +kernel
theorem outside_direction (j : Fin 48) (h : outsideRow j) : pull (rowForm j) (mm (outsideValues j) flip)=ms (outsideScale j) (directionMatrix j) := by
  fin_cases j
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · exact outside_direction_21
  · exact outside_direction_22
  · exact outside_direction_23
  · exact outside_direction_24
  · exact outside_direction_25
  · exact outside_direction_26
  · exact outside_direction_27
  · exact outside_direction_28
  · exact outside_direction_29
  · exact outside_direction_30
  · exact outside_direction_31
  · exact outside_direction_32
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · exact outside_direction_36
  · exact outside_direction_37
  · exact outside_direction_38
  · exact outside_direction_39
  · exact outside_direction_40
  · exact outside_direction_41
  · exact outside_direction_42
  · exact outside_direction_43
  · exact outside_direction_44
  · exact outside_direction_45
  · exact outside_direction_46
  · exact outside_direction_47
theorem outside_determinant (j : Fin 48) (h : outsideRow j) : determinant (outsideValues j)=outsideDeterminant j := by
  fin_cases j
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · exact outside_determinant_21
  · exact outside_determinant_22
  · exact outside_determinant_23
  · exact outside_determinant_24
  · exact outside_determinant_25
  · exact outside_determinant_26
  · exact outside_determinant_27
  · exact outside_determinant_28
  · exact outside_determinant_29
  · exact outside_determinant_30
  · exact outside_determinant_31
  · exact outside_determinant_32
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · exact outside_determinant_36
  · exact outside_determinant_37
  · exact outside_determinant_38
  · exact outside_determinant_39
  · exact outside_determinant_40
  · exact outside_determinant_41
  · exact outside_determinant_42
  · exact outside_determinant_43
  · exact outside_determinant_44
  · exact outside_determinant_45
  · exact outside_determinant_46
  · exact outside_determinant_47
theorem outside_scale_nonzero : ∀ j : Fin 48, outsideRow j → outsideScale j ≠ 0 := by decide +kernel
theorem outside_det_nonzero : ∀ j : Fin 48, outsideRow j → outsideDeterminant j ≠ 0 := by decide +kernel
def ProjectivelyDifferent (U V : Mat) : Prop := ∃ a b c d : Bool, U a b*V c d ≠ U c d*V a b
instance (U V : Mat) : Decidable (ProjectivelyDifferent U V) := by unfold ProjectivelyDifferent; infer_instance
theorem outside_different_21 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 21) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_22 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 22) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_23 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 23) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_24 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 24) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_25 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 25) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_26 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 26) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_27 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 27) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_28 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 28) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_29 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 29) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_30 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 30) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_31 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 31) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_32 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 32) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_36 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 36) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_37 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 37) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_38 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 38) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_39 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 39) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_40 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 40) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_41 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 41) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_42 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 42) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_43 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 43) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_44 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 44) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_45 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 45) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_46 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 46) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different_47 : ∀ k : Fin 24, ProjectivelyDifferent (directionMatrix 47) (standard k) := by
  intro k
  fin_cases k <;> decide +kernel
theorem outside_different (j : Fin 48) (h : outsideRow j) (k : Fin 24) : ProjectivelyDifferent (directionMatrix j) (standard k) := by
  fin_cases j
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · exact outside_different_21 k
  · exact outside_different_22 k
  · exact outside_different_23 k
  · exact outside_different_24 k
  · exact outside_different_25 k
  · exact outside_different_26 k
  · exact outside_different_27 k
  · exact outside_different_28 k
  · exact outside_different_29 k
  · exact outside_different_30 k
  · exact outside_different_31 k
  · exact outside_different_32 k
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · exact outside_different_36 k
  · exact outside_different_37 k
  · exact outside_different_38 k
  · exact outside_different_39 k
  · exact outside_different_40 k
  · exact outside_different_41 k
  · exact outside_different_42 k
  · exact outside_different_43 k
  · exact outside_different_44 k
  · exact outside_different_45 k
  · exact outside_different_46 k
  · exact outside_different_47 k
theorem exit_counts : (Finset.univ.filter endpointRow).card=23 ∧ (Finset.univ.filter equalityRow).card=1 ∧ (Finset.univ.filter outsideRow).card=24 := by decide
end Holant.Certificates.OctahedralSeparator
