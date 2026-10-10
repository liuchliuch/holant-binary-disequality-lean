import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralQuotientGeometry
import Mathlib.Tactic.LinearCombination

/-! Coefficient extraction from the preserved marked-octahedral proof. The eight classes are an OUTPUT of the harmonic
four-point argument. Only fixed integer vectors/permutations are enumerated;
no arbitrary endomorphism atlas or completeness premise is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.HarmonicProjectivities
open scoped Matrix BigOperators

abbrev Plane := Fin 2 → ℂ
abbrev SmallMatrix := Matrix (Fin 2) (Fin 2) ℂ

def rootZ (i : Fin 4) : Fin 2 → ℤ :=
  ![![1,0],![0,1],![1,1],![1,-1]] i

def root (i : Fin 4) : Plane := fun a => (rootZ i a : ℂ)

def cross (u v : Plane) : ℂ := u 0*v 1-u 1*v 0

def det2 (C : SmallMatrix) : ℂ := C 0 0*C 1 1-C 0 1*C 1 0

def crossZ (u v : Fin 2 → ℤ) : ℤ := u 0*v 1-u 1*v 0

def harmonicZ (p : Fin 4 → Fin 4) : ℤ :=
  crossZ (rootZ (p 0)) (rootZ (p 2))*crossZ (rootZ (p 1)) (rootZ (p 3))+
  crossZ (rootZ (p 0)) (rootZ (p 3))*crossZ (rootZ (p 1)) (rootZ (p 2))

def permutation (k : Fin 8) : Fin 4 → Fin 4 :=
  ![![0,1,2,3],![0,1,3,2],![1,0,2,3],![1,0,3,2],
    ![2,3,0,1],![3,2,0,1],![2,3,1,0],![3,2,1,0]] k

/-- Literal parameters I,D,X,DX,H,DH,HD,DHD. These act only on a
two-dimensional proof chart; they are not physical binary gadgets. -/
def parameterZ (k : Fin 8) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![1,0;0,1],!![1,0;0,-1],!![0,1;1,0],!![0,1;-1,0],
    !![1,1;1,-1],!![1,1;-1,1],!![1,-1;1,1],!![1,-1;-1,-1]] k

def parameter (k : Fin 8) : SmallMatrix := fun i j => (parameterZ k i j : ℂ)

def multiplierZ (k : Fin 8) : Fin 4 → ℤ :=
  ![![1,1,1,1],![1,-1,1,1],![1,1,1,-1],![-1,1,1,-1],
    ![1,1,2,2],![1,1,2,-2],![1,-1,2,2],![1,-1,-2,2]] k

theorem permutation_complete : ∀ p : Fin 4 → Fin 4,
    Function.Injective p → harmonicZ p = 0 → ∃ k : Fin 8,p = permutation k := by
  decide +kernel

theorem parameter_action (k : Fin 8) (i : Fin 4) :
    parameter k *ᵥ root i = (multiplierZ k i : ℂ) • root (permutation k i) := by
  fin_cases k <;> fin_cases i <;> ext a <;> fin_cases a <;>
    norm_num [parameter,parameterZ,root,rootZ,multiplierZ,permutation,
      Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem multiplier_ne_zero (k : Fin 8) (i : Fin 4) : (multiplierZ k i : ℂ) ≠ 0 := by
  fin_cases k <;> fin_cases i <;> norm_num [multiplierZ]

theorem parameter_det_ne_zero (k : Fin 8) : det2 (parameter k) ≠ 0 := by
  fin_cases k <;> norm_num [det2,parameter,parameterZ]

theorem cross_smul (a b : ℂ) (u v : Plane) :
    cross (a • u) (b • v) = a*b*cross u v := by
  simp only [cross,Pi.smul_apply,smul_eq_mul]
  ring

theorem map_cross (C : SmallMatrix) (u v : Plane) :
    cross (C *ᵥ u) (C *ᵥ v) = det2 C*cross u v := by
  simp only [cross,det2,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem root_cross_ne {i j : Fin 4} (h : i ≠ j) : cross (root i) (root j) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [root,rootZ,cross] at *

theorem harmonic_cast (p : Fin 4 → Fin 4) : (harmonicZ p : ℂ) =
    cross (root (p 0)) (root (p 2))*cross (root (p 1)) (root (p 3))+
    cross (root (p 0)) (root (p 3))*cross (root (p 1)) (root (p 2)) := by
  simp [harmonicZ,crossZ,cross,root]

def Keeps (C : SmallMatrix) : Prop :=
  ∀ i : Fin 4,∃ j : Fin 4,∃ s : ℂ,s ≠ 0 ∧ C *ᵥ root i = s • root j

def harmonic (v : Fin 4 → Plane) : ℂ :=
  cross (v 0) (v 2)*cross (v 1) (v 3)+cross (v 0) (v 3)*cross (v 1) (v 2)

theorem harmonic_scaled_roots (s : Fin 4 → ℂ) :
    harmonic (fun k => s k • root k) = 0 := by
  simp only [harmonic,cross_smul]
  norm_num [root,rootZ,cross] <;> ring

theorem scaled_roots_separate (s : Fin 4 → ℂ) (hs : ∀ k,s k ≠ 0)
    {i j : Fin 4} (hij : i ≠ j) : cross (s i • root i) (s j • root j) ≠ 0 := by
  rw [cross_smul]
  exact mul_ne_zero (mul_ne_zero (hs i) (hs j)) (root_cross_ne hij)

/-- Three point rigidity, with the scalar computed from the third point.
This proves equality of the same matrix, not just equality of its image set. -/
theorem three_rigidity (C D : SmallMatrix) (hd : det2 D ≠ 0)
    (u v w : ℂ) (h0 : C *ᵥ root 0 = u • (D *ᵥ root 0))
    (h1 : C *ᵥ root 1 = v • (D *ᵥ root 1))
    (h2 : C *ᵥ root 2 = w • (D *ᵥ root 2)) : C = w • D := by
  have h00 : C 0 0 = u*D 0 0 := by
    simpa [root,rootZ,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using congrFun h0 0
  have h10 : C 1 0 = u*D 1 0 := by
    simpa [root,rootZ,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using congrFun h0 1
  have h01 : C 0 1 = v*D 0 1 := by
    simpa [root,rootZ,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using congrFun h1 0
  have h11 : C 1 1 = v*D 1 1 := by
    simpa [root,rootZ,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using congrFun h1 1
  have e0 : u*D 0 0+v*D 0 1 = w*(D 0 0+D 0 1) := by
    have hh := congrFun h2 0
    simpa [root,rootZ,Matrix.mulVec,dotProduct,Fin.sum_univ_two,h00,h01] using hh
  have e1 : u*D 1 0+v*D 1 1 = w*(D 1 0+D 1 1) := by
    have hh := congrFun h2 1
    simpa [root,rootZ,Matrix.mulVec,dotProduct,Fin.sum_univ_two,h10,h11] using hh
  have eu : (u-w)*det2 D = 0 := by
    unfold det2
    linear_combination D 1 1*e0-D 0 1*e1
  have ev : (v-w)*det2 D = 0 := by
    unfold det2
    linear_combination D 0 0*e1-D 1 0*e0
  have hu : u = w := sub_eq_zero.mp ((mul_eq_zero.mp eu).resolve_right hd)
  have hv : v = w := sub_eq_zero.mp ((mul_eq_zero.mp ev).resolve_right hd)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pi.smul_apply,smul_eq_mul,h00,h10,h01,h11,hu,hv]

/-- Completeness for an arbitrary complex projectivity preserving the four
harmonic directions. The finite permutation certificate is proved above. -/
theorem keeps_complete (C : SmallMatrix) (hd : det2 C ≠ 0) (hC : Keeps C) :
    ∃ k : Fin 8,∃ c : ℂ,c ≠ 0 ∧ C = c • parameter k := by
  classical
  choose p s hs he using hC
  have hp : Function.Injective p := by
    intro a b hab
    by_contra hn
    have hz : cross (C *ᵥ root a) (C *ᵥ root b) = 0 := by
      rw [he a,he b,hab,cross_smul]
      simp [cross,mul_comm]
    rw [map_cross] at hz
    exact root_cross_ne hn ((mul_eq_zero.mp hz).resolve_left hd)
  have hh : cross (C *ᵥ root 0) (C *ᵥ root 2)*cross (C *ᵥ root 1) (C *ᵥ root 3)+
      cross (C *ᵥ root 0) (C *ᵥ root 3)*cross (C *ᵥ root 1) (C *ᵥ root 2) = 0 := by
    simp only [map_cross]
    norm_num [root,rootZ,cross] <;> ring
  have hpz : (harmonicZ p : ℂ) = 0 := by
    have hz : (s 0*s 1*s 2*s 3)*(harmonicZ p : ℂ) = 0 := by
      rw [harmonic_cast]
      simp only [he,cross_smul] at hh
      linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 0) (hs 1)) (hs 2)) (hs 3))
  have hpz' : harmonicZ p = 0 := by exact_mod_cast hpz
  obtain ⟨k,hk⟩ := permutation_complete p hp hpz'
  have hi (i : Fin 4) : C *ᵥ root i =
      (s i/(multiplierZ k i : ℂ)) • (parameter k *ᵥ root i) := by
    rw [parameter_action,smul_smul,he i,hk]
    congr 1
    field_simp [multiplier_ne_zero k i]
  refine ⟨k,s 2/(multiplierZ k 2 : ℂ),div_ne_zero (hs 2) (multiplier_ne_zero k 2),?_⟩
  exact three_rigidity C (parameter k) (parameter_det_ne_zero k)
    (s 0/(multiplierZ k 0 : ℂ)) (s 1/(multiplierZ k 1 : ℂ))
    (s 2/(multiplierZ k 2 : ℂ)) (hi 0) (hi 1) (hi 2)

theorem parameter_keeps (k : Fin 8) : Keeps (parameter k) := by
  intro i
  exact ⟨permutation k i,(multiplierZ k i : ℂ),multiplier_ne_zero k i,parameter_action k i⟩

theorem keeps_iff_eight (C : SmallMatrix) (hd : det2 C ≠ 0) :
    Keeps C ↔ ∃ k : Fin 8,∃ c : ℂ,c ≠ 0 ∧ C = c • parameter k := by
  refine ⟨keeps_complete C hd,?_⟩
  rintro ⟨k,c,hc,rfl⟩ i
  refine ⟨permutation k i,c*(multiplierZ k i : ℂ),
    mul_ne_zero hc (multiplier_ne_zero k i),?_⟩
  rw [Matrix.smul_mulVec,parameter_action,smul_smul]

def parameterMinorZ (k l : Fin 8) (a b c d : Fin 2) : ℤ :=
  parameterZ k a b*parameterZ l c d-parameterZ k c d*parameterZ l a b

theorem parameter_separation : ∀ k l : Fin 8,k ≠ l →
    ∃ a b c d : Fin 2,parameterMinorZ k l a b c d ≠ 0 := by
  decide +kernel

/-- Eight distinct projective classes, not an eight-entry list with
unproved duplications. The finite separation certificate is an output. -/
theorem parameter_class_unique {k l : Fin 8} {c d : ℂ} (hc : c ≠ 0)
    (he : c • parameter k = d • parameter l) : k = l := by
  by_contra hn
  obtain ⟨a,b,i,j,hm⟩ := parameter_separation k l hn
  have h0 : c*parameter k a b = d*parameter l a b :=
    congrFun (congrFun he a) b
  have h1 : c*parameter k i j = d*parameter l i j :=
    congrFun (congrFun he i) j
  have hz : c*(parameterMinorZ k l a b i j : ℂ) = 0 := by
    simp only [parameterMinorZ,Int.cast_sub,Int.cast_mul]
    change c*(parameter k a b*parameter l i j-parameter k i j*parameter l a b) = 0
    linear_combination parameter l i j*h0-parameter l a b*h1
  have hm' : (parameterMinorZ k l a b i j : ℂ) ≠ 0 := by exact_mod_cast hm
  exact (mul_ne_zero hc hm') hz

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.HarmonicProjectivities
