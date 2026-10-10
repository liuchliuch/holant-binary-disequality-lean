import Holant.Platonic.RankDeficientLocalization.FixedMatching
import Holant.Certificates.PlatonicAtlas.Spanning

/-! Matching equality for all actual kernels and its exact finite-domain
presentation. Coverage prevents replacing the domain by a smaller graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RankDeficientLocalization
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Platonic.RainbowLocalization
variable {P : Type*} [Fintype P] [DecidableEq P]

def actualDomain (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat) : Set (Kernel ℂ) :=
  Set.range (fun i : Fin (size g) => e (representative g i))

def CommonActualMatching (Φ : Mat→ₗ[ℂ]Tensor ℂ P) (D : Set (Kernel ℂ)) : Prop :=
  ∃m : Equiv.Perm P,∀K∈D,∀C : NonsingularCard (Φ K),C.matching=m

/-- Same actual tensor up to scalar has the same residual mate involution. -/
theorem NonsingularCard.matching_eq_of_smul {F H : Tensor ℂ P}
    (C : NonsingularCard F) (E : NonsingularCard H) (c : ℂ) (he : F=c • H) :
    C.matching=E.matching := by
  apply matching_eq_of_tensor_smul C.presentation E.presentation C.det_ne_zero E.det_ne_zero
    C.scalar_ne_zero E.scalar_ne_zero c
  rw [←C.value,←E.value]
  exact he

/-- This equivalence allows arbitrary recorded nonzero representative scales.
No matching labels occur in either the availability or coverage assumptions. -/
theorem common_actual_iff_domain (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat)
    (Φ : Mat→ₗ[ℂ]Tensor ℂ P) (D : Set (Kernel ℂ))
    (hactual : ∀i,e (representative g i)∈D)
    (hcover : ∀K∈D,∃i : Fin (size g),∃c : ℂ,c≠0 ∧ K=c • e (representative g i))
    (hcards : ∀i,Φ (e (representative g i))=0 ∨
      Nonempty (NonsingularCard (Φ (e (representative g i))))) :
    CommonActualMatching Φ D ↔ CommonMatching Φ g e := by
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,fun i C => hm _ (hactual i) C⟩
  · rintro ⟨m,hm⟩
    refine ⟨m,?_⟩
    intro K hK C
    obtain ⟨i,c,hc,he⟩ := hcover K hK
    have hv : Φ K=c • Φ (e (representative g i)) := by rw [he,map_smul]
    have hn : Φ (e (representative g i))≠0 := by
      intro hz
      exact C.nonzero (by rw [hv,hz,smul_zero])
    obtain ⟨E⟩ := (hcards i).resolve_left hn
    exact (C.matching_eq_of_smul E c hv).trans (hm i E)

theorem actualDomain_member (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat) (i : Fin (size g)) :
    e (representative g i)∈actualDomain g e := ⟨i,rfl⟩

theorem actualDomain_cover (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat)
    (K : Kernel ℂ) (hK : K∈actualDomain g e) :
    ∃i : Fin (size g),∃c : ℂ,c≠0 ∧ K=c • e (representative g i) := by
  obtain ⟨i,rfl⟩ := hK
  exact ⟨i,1,one_ne_zero,by simp⟩

/-- Spanning of the exact literal actual domain is derived from the four
quaternion axes and transported linearly; it is not a source assumption. -/
theorem actualDomain_span (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat) :
    Submodule.span ℂ (actualDomain g e)=⊤ := by
  have hm : Submodule.span ℂ (Set.range (fun i : Fin (size g) => e (representative g i)) : Set Mat)=⊤ := by
    apply top_unique
    rw [←Holant.Certificates.PlatonicAtlas.transported_sourceAxes_span e]
    apply Submodule.span_le.mpr
    rintro z ⟨i,rfl⟩
    obtain ⟨j,c,hc,hj⟩ := (complete g (Holant.Certificates.PlatonicAtlas.sourceAxes i)).mp
      (Holant.Certificates.PlatonicAtlas.sourceAxes_actual g i)
    change e (Holant.Certificates.PlatonicAtlas.sourceAxes i) ∈ _
    have hej : e (Holant.Certificates.PlatonicAtlas.sourceAxes i)=c • e (representative g j) :=
      (congrArg e hj).trans (e.map_smul c (representative g j))
    exact hej.symm ▸ Submodule.smul_mem _ c (Submodule.subset_span ⟨j,rfl⟩)
  exact hm

end Holant.Platonic.RankDeficientLocalization
