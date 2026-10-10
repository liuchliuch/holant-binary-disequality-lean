import Holant.Platonic.RankDeficientLocalization.RichLine
import Holant.Platonic.RainbowLocalization.SourceEncoded
import Holant.Platonic.RainbowLocalization.PhysicalSelected

/-! Intrinsic card-map ranks of the literal six-port localization graph.
The post-map is actual disjoint contraction with all representative scales. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RankDeficientLocalization
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.MatchingContractionClosure
open Holant.Platonic.RainbowLocalization Holant.Platonic.RainbowLocalization.Physical
open scoped BigOperators
variable {P Q E : Type*} [Fintype E] [DecidableEq E] [DecidableEq P]

def closureLinear (p : CollectionPorts P Q E) (C : E→Kernel ℂ) :
    Tensor ℂ P →ₗ[ℂ] Tensor ℂ Q where
  toFun := contractCollection p C
  map_add' f g := by
    funext x
    simp only [contractCollection,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [contractCollection,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro y hy
    ring

variable {n : ℕ} [Fintype P] {Λ : SignatureFamily ℂ} {D : Set (Kernel ℂ)}
variable {D₀ D₁ D₂ : Presentation ℂ P}

def localizationPostMap (A : ActualKernelLift Λ D) (L : AlgebraicLocalization D₀ D₁ D₂)
    (C : Fin L.common.edges→D) :
    Tensor ℂ P →ₗ[ℂ] Tensor ℂ (MatchingCut.Side (MatchingCut.cut L.ports) true) :=
  realizationScale A C • closureLinear (localizedPorts L) (fun i => (C i).val)

/-- Exact equality of linear maps, with the retained original ordered pair
and the actual six surviving physical ports. -/
theorem localization_cardMap_comp (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges→D) (f : Signature ℂ n) :
    cardMap (sixPortOrder L) (localizationSignature A L p C f)=
      (localizationPostMap A L C).comp (cardMap p f) := by
  apply LinearMap.ext
  intro K
  change cardMap (sixPortOrder L) (localizationSignature A L p C f) K =
    realizationScale A C • contractCollection (localizedPorts L) (fun i => (C i).val) (cardMap p f K)
  rw [localizationSignature,localizationNetwork,actualCollection_denote,cardMap_smul_tensor,
    originalClosurePorts,cardMap_full_closure]

/-- Physical localization cannot increase the ancestor card-map rank. -/
theorem localization_rank_le (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges→D) (f : Signature ℂ n) :
    Module.finrank ℂ (cardMap (sixPortOrder L) (localizationSignature A L p C f)).range ≤
      Module.finrank ℂ (cardMap p f).range := by
  rw [localization_cardMap_comp,LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

/-- Every ancestor kernel remains a kernel after the literal graph closure. -/
theorem localization_kernel_le (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges→D) (f : Signature ℂ n) :
    (cardMap p f).ker ≤ (cardMap (sixPortOrder L) (localizationSignature A L p C f)).ker := by
  rw [localization_cardMap_comp]
  exact LinearMap.ker_le_ker_comp _ _

/-- The surviving selected cards prove rank at least two, from their actual
nonzero matching tensors, without an assumed rank certificate. -/
theorem localization_rank_ge_two (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges→D) (f : Signature ℂ n) (hs : localizationScale A L C≠0)
    (K₀ K₁ : Kernel ℂ)
    (h₀ : cardMap (sixPortOrder L) (localizationSignature A L p C f) K₀=
      localizationScale A L C • L.exceptional₀.tensor)
    (h₁ : cardMap (sixPortOrder L) (localizationSignature A L p C f) K₁=
      localizationScale A L C • L.exceptional₁.tensor) :
    2≤Module.finrank ℂ (cardMap (sixPortOrder L) (localizationSignature A L p C f)).range := by
  have hn₀ : L.exceptional₀.tensor≠0 := productValue_nonzero _ _ _ L.exceptional₀_det L.exceptional₀_scalar
  have hn₁ : L.exceptional₁.tensor≠0 := productValue_nonzero _ _ _ L.exceptional₁_det L.exceptional₁_scalar
  have hp₀ : Proportional
      (cardMap (sixPortOrder L) (localizationSignature A L p C f) K₀) L.exceptional₀.tensor := ⟨_,hs,h₀⟩
  have hp₁ : Proportional
      (cardMap (sixPortOrder L) (localizationSignature A L p C f) K₁) L.exceptional₁.tensor := ⟨_,hs,h₁⟩
  apply rank_ge_two_of_nonproportional _ K₀ K₁
  · rw [h₀]; exact smul_ne_zero hs hn₀
  · rw [h₁]; exact smul_ne_zero hs hn₁
  · intro hp
    exact (exceptional_projectively_distinct L).1 (hp₀.symm.trans (hp.trans hp₁))

theorem localization_rank_bounds (A : ActualKernelLift Λ D)
    (L : AlgebraicLocalization D₀ D₁ D₂) (p : Bool ⊕ P ≃ Fin n)
    (C : Fin L.common.edges→D) (f : Signature ℂ n) (hs : localizationScale A L C≠0)
    (K₀ K₁ : Kernel ℂ)
    (h₀ : cardMap (sixPortOrder L) (localizationSignature A L p C f) K₀=
      localizationScale A L C • L.exceptional₀.tensor)
    (h₁ : cardMap (sixPortOrder L) (localizationSignature A L p C f) K₁=
      localizationScale A L C • L.exceptional₁.tensor) :
    2≤Module.finrank ℂ (cardMap (sixPortOrder L) (localizationSignature A L p C f)).range ∧
    Module.finrank ℂ (cardMap (sixPortOrder L) (localizationSignature A L p C f)).range≤
      Module.finrank ℂ (cardMap p f).range ∧
    Module.finrank ℂ (cardMap p f).range≤4 :=
  ⟨localization_rank_ge_two A L p C f hs K₀ K₁ h₀ h₁,
    localization_rank_le A L p C f,map_rank_le_four (cardMap p f)⟩

end Holant.Platonic.RankDeficientLocalization
