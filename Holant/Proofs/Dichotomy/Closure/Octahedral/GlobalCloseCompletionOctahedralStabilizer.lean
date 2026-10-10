import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralOrbitIndices

/-! Coefficient extraction from the preserved marked-octahedral proof. The eight harmonic parameters are restrictions of
eight explicit pairs of ACTUAL old O kernels. The fixed arithmetic check
has four marked rows, eight pairs and two basis vectors; it does not check
arbitrary tensors or assume a finite projectivity classification. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.PhysicalOrbit
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.TetrahedralPreservers Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.HarmonicProjectivities
open scoped Matrix

def stabilizerPair : Fin 8 → Fin 24 × Fin 24 :=
  ![(0,0),(2,2),(2,3),(1,0),(23,2),(13,0),(12,0),(22,2)]

def stabilizerSign : Fin 8 → ℤ := ![1,-1,-1,-1,-1,1,1,-1]

theorem stabilizerSign_ne : ∀ k : Fin 8,(stabilizerSign k : Scalar) ≠ 0 := by
  intro k
  fin_cases k <;> decide +kernel

private theorem mm_ms_left (c : Scalar) (U V : OctahedralSeparator.Mat) :
    mm (ms c U) V=ms c (mm U V) := by
  funext a b
  simp only [mm,ms]
  ring

private theorem rawCoordinates_ms (c : Scalar) (U : OctahedralSeparator.Mat) :
    RankThree.rawCoordinates (ms c U)=c • RankThree.rawCoordinates U := by
  funext i
  fin_cases i <;> simp [RankThree.rawCoordinates,ms,Pi.smul_apply,smul_eq_mul] <;> ring

theorem finite_stabilizer : ∀ f : Form,∀ k : Fin 8,∀ a : Fin 2,
    RankThree.rawCoordinates
      (mm (mm (theta f (OctahedralSeparator.standard (stabilizerPair k).1))
        (theta f (OctahedralSeparator.standard (if a = 0 then 0 else 1))))
        (theta f (OctahedralSeparator.standard (stabilizerPair k).2))) =
      (stabilizerSign k : Scalar) •
        ((parameterZ k 0 a : Scalar) • rawPoint f 0 +
          (parameterZ k 1 a : Scalar) • rawPoint f 1) := by
  intro f k a
  rw [←theta_mm,←theta_mm,Products.standard_product,mm_ms_left,
    Products.standard_product,theta_ms,theta_ms,rawCoordinates_ms,rawCoordinates_ms,
    ←RankThree.rawPoint_exact]
  fin_cases f <;> fin_cases k <;> fin_cases a <;> decide +kernel

noncomputable section

theorem stabilizer_scalar_ne (k : Fin 8) : embed (stabilizerSign k : Scalar) ≠ 0 :=
  fun h => stabilizerSign_ne k (embed_injective (h.trans embed_zero.symm))

theorem stabilizer_column (f : Form) (k : Fin 8) (a : Fin 2) :
    sandwich (kernel f (stabilizerPair k).1) (kernel f (stabilizerPair k).2) *ᵥ
      point f (if a = 0 then 0 else 1) =
      embed (stabilizerSign k : Scalar) •
        (parameter k 0 a • point f 0 + parameter k 1 a • point f 1) := by
  have h := congrArg RankThree.lift (finite_stabilizer f k a)
  rw [RankThree.lift_rawCoordinates,complexMatrix_mm,complexMatrix_mm,
    RankThree.lift_smul,RankThree.lift_add,RankThree.lift_smul,
    RankThree.lift_smul,RankThree.lift_point,RankThree.lift_point] at h
  have he (i j : Fin 2) : embed (parameterZ k i j : Scalar) = parameter k i j := by
    change embedding (parameterZ k i j : Scalar) = (parameterZ k i j : ℂ)
    simp
  rw [he,he] at h
  rw [sandwich_action]
  change coordinates (kernel f (stabilizerPair k).1 *
    assemble (quaternionCoefficient (kernel f (if a = 0 then 0 else 1))) *
      kernel f (stabilizerPair k).2) = _
  rw [assemble_coefficient]
  exact h

/-- Full plane action, not just a permutation of the four labels. -/
theorem stabilizer_chart (f : Form) (k : Fin 8) :
    sandwich (kernel f (stabilizerPair k).1) (kernel f (stabilizerPair k).2) *
      lineMatrix f baseLine =
      embed (stabilizerSign k : Scalar) • (lineMatrix f baseLine * parameter k) := by
  ext i a
  fin_cases a
  · have h := congrFun (stabilizer_column f k (0 : Fin 2)) i
    simpa [lineMatrix,base_pair,Matrix.mul_apply,Matrix.mulVec,dotProduct,
      Fin.sum_univ_two,smul_eq_mul,mul_add,mul_comm] using h
  · have h := congrFun (stabilizer_column f k (1 : Fin 2)) i
    simpa [lineMatrix,base_pair,Matrix.mul_apply,Matrix.mulVec,dotProduct,
      Fin.sum_univ_two,smul_eq_mul,mul_add,mul_comm] using h

/-- The previous harmonic completeness theorem is consumed here: EVERY
projectivity preserving the four directions is a scalar restriction of an
actual old kernel pair. The pair and multiplier are outputs of the proof. -/
theorem complete_actual_stabilizer (f : Form) (C : SmallMatrix)
    (hd : det2 C ≠ 0) (hc : Keeps C) :
    ∃ k : Fin 8,∃ c : ℂ,c ≠ 0 ∧
      lineMatrix f baseLine * C = c •
        (sandwich (kernel f (stabilizerPair k).1) (kernel f (stabilizerPair k).2) *
          lineMatrix f baseLine) := by
  obtain ⟨k,d,hd',he⟩ := keeps_complete C hd hc
  let z := embed (stabilizerSign k : Scalar)
  have hz : z ≠ 0 := stabilizer_scalar_ne k
  refine ⟨k,d/z,div_ne_zero hd' hz,?_⟩
  rw [he,Matrix.mul_smul,stabilizer_chart,smul_smul]
  congr 1
  exact (div_mul_cancel₀ d hz).symm

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.PhysicalOrbit
