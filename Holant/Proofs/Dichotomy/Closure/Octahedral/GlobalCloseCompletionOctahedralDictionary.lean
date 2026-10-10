import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralRigidity
import Holant.Certificates.PlatonicIncidence.BaseSecants

/-! Coefficient extraction from the preserved marked-octahedral proof. Literal F4 dictionary and its identity secants.
Only 24 roots and three coordinates are checked, using ordinary kernel
decide. This is not enumeration or assumed completeness of arbitrary maps.
No generator, native_decide, new matrix alphabet or budget increase. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open scoped BigOperators Matrix

def plus (i : Fin 3) : Fin 24 := ⟨12+2*i.val,by omega⟩
def minus (i : Fin 3) : Fin 24 := ⟨13+2*i.val,by omega⟩

theorem point_zero_representative (k : Fin 24) :
    point 0 k = coordinates (representative .octahedral k) := by
  have h0 : complexMatrix (conjugator 0) = 1 := by
    simpa only [conjugator,Matrix.cons_val_zero] using complexMatrix_q0
  simp only [point,kernel,complexMatrix_theta,complexTheta,h0,
    inv_one,Matrix.one_mul,Matrix.mul_one]
  rw [←octahedralRaw_standard]
  rfl

theorem point_zero_table (k : Fin 24) : point 0 k = liftVector (zOcta k) := by
  rw [point_zero_representative]
  ext i
  change coordinates (goldenMatrix (raw .octahedral k)) i = liftVector (zOcta k) i
  rw [coordinates_golden]
  fin_cases k <;> fin_cases i <;>
    norm_num [raw,octahedralRaw,GoldenInt.eval,liftVector,zOcta]

theorem point_zero_axis (i : Fin 4) : point 0 (axis i) = Pi.single i 1 := by
  rw [point_zero_table]
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [axis,liftVector,zOcta,Pi.single_apply]

theorem point_plus (i : Fin 3) : point 0 (plus i) =
    Pi.single (0 : Fin 4) 1 + Pi.single i.succ 1 := by
  rw [point_zero_table]
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [plus,liftVector,zOcta,Pi.single_apply]

theorem point_minus (i : Fin 3) : point 0 (minus i) =
    Pi.single (0 : Fin 4) 1 - Pi.single i.succ 1 := by
  rw [point_zero_table]
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [minus,liftVector,zOcta,Pi.single_apply]

private theorem coordinates_span_pair (U W Z : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) :
    coordinates Z ∈ Submodule.span ℂ ({coordinates U,coordinates W} : Set V) ↔
      Z ∈ Submodule.span ℂ ({U,W} : Set Holant.Certificates.TetrahedralPreservers.BinaryMatrix) := by
  constructor
  · intro h
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨a,b,coordinates.injective ?_⟩
    simpa only [map_add,map_smul] using he
  · intro h
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp h
    exact Submodule.mem_span_pair.mpr ⟨a,b,by
      simpa only [map_add,map_smul] using congrArg coordinates he⟩

theorem actual_baseSecant (k : Fin 24) (hk : k ≠ 0) :
    secant 0 0 k = baseSecant .octahedral k := by
  classical
  ext j
  rw [mem_secant,baseSecant_iff .octahedral k j hk,
    point_zero_representative,point_zero_representative,point_zero_representative]
  have hi : representative .octahedral (0 : Fin 24) = 1 :=
    representative_identity .octahedral
  rw [hi]
  exact coordinates_span_pair _ _ _

/-- Complete identity-rich-four-line classification of the old 24 roots.
There is no preserver/candidate/permutation as a premise of this check. -/
theorem rich_four_indices (k : Fin 24) : k ≠ 0 →
    (baseSecant .octahedral k).card = 4 →
      (∃ i : Fin 3, k = axis i.succ) ∨
      (∃ i : Fin 3, k = plus i) ∨ (∃ i : Fin 3, k = minus i) := by
  fin_cases k <;> decide

theorem axis_secant_card (i : Fin 3) :
    (baseSecant .octahedral (axis i.succ)).card = 4 := by
  fin_cases i <;> decide

private theorem raw_coordinate_alternatives (k : Fin 24) (i : Fin 3) :
    zOcta k i.succ ≠ 0 →
      zOcta k 0 = 0 ∨ zOcta k 0 = zOcta k i.succ ∨
        zOcta k 0 = -(zOcta k i.succ) := by
  fin_cases k <;> fin_cases i <;> decide

/-- A genuine arbitrary complex root receipt; the scales are not assumed
to be integral or normalized. -/
theorem root_coordinate_alternatives {v : V} (hv : v ∈ Roots 0)
    (i : Fin 3) (hi : v i.succ ≠ 0) :
    v 0 = 0 ∨ v 0 = v i.succ ∨ v 0 = -v i.succ := by
  obtain ⟨k,c,hc,rfl⟩ := (roots_iff 0 v).mp hv
  rw [point_zero_table] at hi ⊢
  have hk : zOcta k i.succ ≠ 0 := by
    intro hz
    exact hi (by simp only [Pi.smul_apply,liftVector,hz,Int.cast_zero,smul_eq_mul,mul_zero])
  rcases raw_coordinate_alternatives k i hk with hz | he | he
  · left
    simp only [Pi.smul_apply,liftVector,hz,Int.cast_zero,smul_eq_mul,mul_zero]
  · right; left
    simpa only [Pi.smul_apply,liftVector,smul_eq_mul] using
      congrArg (fun n : ℤ => c*(n : ℂ)) he
  · right; right
    simpa only [Pi.smul_apply,liftVector,smul_eq_mul,Int.cast_neg,mul_neg] using
      congrArg (fun n : ℤ => c*(n : ℂ)) he

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
