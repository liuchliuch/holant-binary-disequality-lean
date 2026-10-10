import Holant.Certificates.PlatonicIncidence.Coordinates
import Holant.Certificates.RainbowOrbit.ExternalSource
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The literal coefficient space and bilinear Frobenius adjoint of source
Proposition 9.27. Projective points are represented by their complete nonzero
scalar saturations. No classification of preservers is assumed here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open scoped BigOperators Matrix

abbrev V := Fin 4 → ℂ
abbrev End := Matrix (Fin 4) (Fin 4) ℂ
abbrev BinaryMatrix := Matrix Bool Bool ℂ

/-- The actual projective coefficient set of a saturated matrix set. -/
def CoefficientSet (S : Set BinaryMatrix) : Set V := coordinates '' S

theorem mem_coefficientSet_iff (S : Set BinaryMatrix) (r : V) :
    r ∈ CoefficientSet S ↔ assemble r ∈ S := by
  constructor
  · rintro ⟨K,hK,rfl⟩
    change assemble (quaternionCoefficient K) ∈ S
    simpa only [assemble_coefficient] using hK
  · intro h
    exact ⟨assemble r,h,coefficient_assemble r⟩

def Standard : Set V := CoefficientSet {K | groupDirection .tetrahedral K}
def External : Set V := CoefficientSet {K | RainbowOrbit.External.Direction K}

def standardPoint (k : Fin 12) : V :=
  coordinates (RainbowOrbit.representative .tetrahedral k)
def externalPoint (k : Fin 12) : V :=
  coordinates (RainbowOrbit.External.representative k)

theorem standard_iff (r : V) : r ∈ Standard ↔
    ∃ k : Fin 12, ∃ c : ℂ, c ≠ 0 ∧ r = c • standardPoint k := by
  rw [Standard,mem_coefficientSet_iff,Set.mem_setOf_eq,RainbowOrbit.complete]
  constructor
  · rintro ⟨k,c,hc,h⟩
    refine ⟨k,c,hc,?_⟩
    have hh := congrArg coordinates h
    change quaternionCoefficient (assemble r) = coordinates (c • _) at hh
    simpa only [coefficient_assemble,map_smul,standardPoint] using hh
  · rintro ⟨k,c,hc,rfl⟩
    refine ⟨k,c,hc,?_⟩
    change coordinates.symm (c • coordinates _) = _
    simp

theorem external_iff (r : V) : r ∈ External ↔
    ∃ k : Fin 12, ∃ c : ℂ, c ≠ 0 ∧ r = c • externalPoint k := by
  rw [External,mem_coefficientSet_iff]
  constructor
  · rintro ⟨k,c,hc,h⟩
    refine ⟨k,c,hc,?_⟩
    have hh := congrArg coordinates h
    change quaternionCoefficient (assemble r) = coordinates (c • _) at hh
    simpa only [coefficient_assemble,map_smul,externalPoint] using hh
  · rintro ⟨k,c,hc,rfl⟩
    refine ⟨k,c,hc,?_⟩
    change coordinates.symm (c • coordinates _) = _
    simp

/-- Closure under precisely the changes of nonzero projective representative. -/
def Saturated (S : Set V) : Prop :=
  ∀ ⦃r : V⦄, r ∈ S → ∀ ⦃c : ℂ⦄, c ≠ 0 → c • r ∈ S

theorem standard_saturated : Saturated Standard := by
  intro r hr c hc
  obtain ⟨k,d,hd,rfl⟩ := (standard_iff r).mp hr
  exact (standard_iff _).mpr ⟨k,c*d,mul_ne_zero hc hd,by rw [smul_smul]⟩

theorem external_saturated : Saturated External := by
  intro r hr c hc
  obtain ⟨k,d,hd,rfl⟩ := (external_iff r).mp hr
  exact (external_iff _).mpr ⟨k,c*d,mul_ne_zero hc hd,by rw [smul_smul]⟩

def frobeniusSigns : V := ![1,-1,1,-1]
/-- This is literally diag(1,-1,1,-1), with no Hermitian conjugation. -/
def J : End := Matrix.diagonal frobeniusSigns
def sharp (A : End) : End := J * A.transpose * J

@[simp] theorem signs_square (i : Fin 4) : frobeniusSigns i * frobeniusSigns i = 1 := by
  fin_cases i <;> norm_num [frobeniusSigns]

@[simp] theorem J_transpose : J.transpose = J := by
  ext i j
  by_cases h : i=j
  · subst j; simp [J,Matrix.transpose_apply]
  · simp [J,Matrix.transpose_apply,Matrix.diagonal,h,Ne.symm h]
@[simp] theorem J_square : J * J = 1 := by
  rw [J,Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal,Matrix.one_apply]

theorem sharp_apply (A : End) (i j : Fin 4) :
    sharp A i j = frobeniusSigns i * A j i * frobeniusSigns j := by
  simp [sharp,J,Matrix.diagonal_mul,Matrix.mul_diagonal]

@[simp] theorem sharp_sharp (A : End) : sharp (sharp A) = A := by
  simp only [sharp,Matrix.transpose_mul,J_transpose,Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc J J,J_square,Matrix.one_mul,
    Matrix.mul_one]

theorem sharp_mul (A B : End) : sharp (A*B) = sharp B * sharp A := by
  simp only [sharp,Matrix.transpose_mul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc J J,J_square,Matrix.one_mul]

@[simp] theorem sharp_zero : sharp 0 = 0 := by simp [sharp]
@[simp] theorem sharp_one : sharp 1 = 1 := by simp [sharp]
@[simp] theorem sharp_smul (c : ℂ) (A : End) : sharp (c • A) = c • sharp A := by
  simp [sharp,Matrix.transpose_smul,Matrix.mul_smul,Matrix.smul_mul]

def pairing (r s : V) : ℂ := ∑ i, frobeniusSigns i * r i * s i

/-- The literal Frobenius form has Gram matrix 2J in quaternion coordinates. -/
theorem frobenius_pairing (U W : BinaryMatrix) :
    (∑ a : Bool, ∑ b : Bool, U a b * W a b) =
      2 * pairing (coordinates U) (coordinates W) := by
  simp [pairing,frobeniusSigns,Fin.sum_univ_succ,coordinates_apply,quaternionCoefficient]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem pairing_adjoint (A : End) (r s : V) :
    pairing (A *ᵥ r) s = pairing r (sharp A *ᵥ s) := by
  simp [pairing,Matrix.mulVec, dotProduct,sharp_apply,
    Fin.sum_univ_succ,frobeniusSigns]
  ring

def OneSided (S : Set V) (A : End) : Prop :=
  ∀ r ∈ S, A *ᵥ r = 0 ∨ A *ᵥ r ∈ S

def TwoSided (S : Set V) (A : End) : Prop :=
  OneSided S A ∧ OneSided S (sharp A)

/-- Both zero alternatives and nonzero image classes are representative-independent. -/
theorem representative_independent {S : Set V} (hS : Saturated S)
    (A : End) (r : V) {c : ℂ} (hc : c ≠ 0) :
    (A *ᵥ (c • r) = 0 ∨ A *ᵥ (c • r) ∈ S) ↔
      (A *ᵥ r = 0 ∨ A *ᵥ r ∈ S) := by
  rw [Matrix.mulVec_smul]
  constructor
  · rintro (h | h)
    · exact Or.inl ((smul_eq_zero.mp h).resolve_left hc)
    · have hh := hS h (inv_ne_zero hc)
      simpa [smul_smul,hc] using Or.inr hh
  · rintro (h | h)
    · simp [h]
    · exact Or.inr (hS h hc)

theorem twoSided_representative_independent {S : Set V} (hS : Saturated S)
    (A : End) (r : V) {c : ℂ} (hc : c ≠ 0) :
    ((A *ᵥ (c • r) = 0 ∨ A *ᵥ (c • r) ∈ S) ∧
      (sharp A *ᵥ (c • r) = 0 ∨ sharp A *ᵥ (c • r) ∈ S)) ↔
    ((A *ᵥ r = 0 ∨ A *ᵥ r ∈ S) ∧
      (sharp A *ᵥ r = 0 ∨ sharp A *ᵥ r ∈ S)) := by
  rw [representative_independent hS A r hc,representative_independent hS (sharp A) r hc]

@[simp] theorem twoSided_zero (S : Set V) : TwoSided S 0 := by
  constructor <;> intro r hr <;> simp

theorem oneSided_comp {S : Set V} {A B : End} (hA : OneSided S A)
    (hB : OneSided S B) : OneSided S (A*B) := by
  intro r hr
  rw [← Matrix.mulVec_mulVec]
  rcases hB r hr with h | h
  · simp [h]
  · exact hA _ h

theorem twoSided_comp {S : Set V} {A B : End} (hA : TwoSided S A)
    (hB : TwoSided S B) : TwoSided S (A*B) := by
  exact ⟨oneSided_comp hA.1 hB.1,by rw [sharp_mul]; exact oneSided_comp hB.2 hA.2⟩

end Holant.Certificates.TetrahedralPreservers
