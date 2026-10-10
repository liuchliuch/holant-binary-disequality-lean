import Holant.Platonic.RankDeficientLocalization.Normalization.DomainActions
import Holant.Certificates.OctahedralSeparator.CaseIndex

/-! The unordered A.19 domain orbit can be ordered arbitrarily by actual
left/right group matrices and a possible swap of the contracted pair. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def triangleRotation (g : PlatonicModel) (r : Fin 3) : DomainAction g where
  left := normalTriangle r
  right := 1
  swap := false
  left_mem := normalTriangle_mem g r
  right_mem := direction_one g

def triangleReflection (g : PlatonicModel) : DomainAction g where
  left := Matrix.of Q2
  right := -(Matrix.of Q2)
  swap := true
  left_mem := quaternion_axis_direction g 2
  right_mem := by
    have hh := groupDirection_smul g
      (show groupDirection g (Matrix.of Q2) from quaternion_axis_direction g 2)
      (by norm_num : (-1 : ℂ)≠0)
    exact (by simpa only [neg_one_smul] using hh)

def triangleFrame (g : PlatonicModel) : Fin 6 → DomainAction g :=
  ![triangleRotation g 2,triangleRotation g 0,triangleRotation g 1,
    (triangleRotation g 1).comp (triangleReflection g),triangleReflection g,
    (triangleRotation g 0).comp (triangleReflection g)]

def triangleScale : Fin 6 → Fin 3 → ℂ :=
  ![![1,1,1],![-2,4,1],![4,-2,1],![-2,4,1],![1,1,1],![4,-2,1]]

theorem triangleScale_ne_zero (p : Fin 6) (r : Fin 3) : triangleScale p r≠0 := by
  fin_cases p <;> fin_cases r <;> norm_num [triangleScale]

theorem triangleFrame_exact (g : PlatonicModel) (p : Fin 6) (r : Fin 3) :
    (triangleFrame g p).apply (normalTriangle r)=
      triangleScale p r • normalTriangle (OctahedralSeparator.permutations p r) := by
  fin_cases p <;> fin_cases r <;> ext a b <;> cases a <;> cases b <;>
    simp [triangleFrame,triangleRotation,triangleReflection,DomainAction.comp,DomainAction.apply,
      normalTriangle,triangleScale,OctahedralSeparator.permutations,
      TetrahedralBridge.normalPlus,TetrahedralBridge.normalMinus,
      Q0,Q1,Q2,Q3,Signature.equality,Matrix.mul_apply] <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem domain_ordering (g : PlatonicModel) (σ : Equiv.Perm (Fin 3)) :
    ∃ D : DomainAction g, ∃ c : Fin 3 → ℂ, (∀r,c r≠0) ∧
      ∀r,D.apply (normalTriangle r)=c r • normalTriangle (σ r) := by
  obtain ⟨p,hp⟩ := (OctahedralSeparator.permutations_complete σ).mp σ.bijective
  refine ⟨triangleFrame g p,triangleScale p,triangleScale_ne_zero p,?_⟩
  intro r
  rw [triangleFrame_exact,←hp]

end
end Holant.Platonic.RankDeficientLocalization.Normalization
