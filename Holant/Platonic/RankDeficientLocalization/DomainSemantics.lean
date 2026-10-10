import Holant.Platonic.RankDeficientLocalization.RichLine

/-! Literal projective semantics and the uncoloured ruling/rainbow dichotomy. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RankDeficientLocalization
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Platonic.RainbowLocalization
open scoped Classical
variable {P : Type*} [Fintype P] [DecidableEq P] {n : ℕ}
variable {Φ : Mat→ₗ[ℂ] Tensor ℂ P} {U : Fin n→Mat}

theorem RainbowDomainLine.intersection_card (R : RainbowDomainLine Φ U) :
    (matrixIntersection U (Submodule.span ℂ ({U R.first,U R.second} : Set Mat))).card=3 := by
  classical
  rw [R.exact_points]
  simp [R.first_ne_second,R.third_ne_first,R.third_ne_second,Ne.symm R.third_ne_first,
    Ne.symm R.third_ne_second]

theorem RainbowDomainLine.projective_intersection_card (R : RainbowDomainLine Φ U)
    (hU : ∀i,U i≠0) (hf : ∀i j (c : ℂ),U i=c • U j→i=j) :
    ((projectiveDictionary U hU).filter (fun z => z∈
      (Submodule.span ℂ ({U R.first,U R.second} : Set Mat)).projectivization)).card=3 := by
  rw [Holant.Certificates.PlatonicIncidence.projective_intersection_card U hU hf]
  exact R.intersection_card

theorem RainbowDomainLine.restriction_rank (R : RainbowDomainLine Φ U) :
    Module.finrank ℂ
      ((Submodule.span ℂ ({U R.first,U R.second} : Set Mat)).map Φ)=2 := by
  rw [Submodule.map_span,Set.image_pair]
  exact nonproportional_span_pair_finrank _ _ R.card₀.nonzero R.card₁.nonzero
    (R.card₀.not_proportional R.card₁ R.different₀₁)

theorem RainbowDomainLine.domain_dimension (R : RainbowDomainLine Φ U)
    (hU : ∀i,U i≠0) (hf : ∀i j (c : ℂ),U i=c • U j→i=j) :
    Module.finrank ℂ (Submodule.span ℂ ({U R.first,U R.second} : Set Mat))=2 :=
  matrix_pair_dimension U hU hf R.first R.second R.first_ne_second

theorem RainbowDomainLine.whole_line_injective (R : RainbowDomainLine Φ U) :
    Set.InjOn Φ (Submodule.span ℂ ({U R.first,U R.second} : Set Mat)) :=
  LinearMap.injOn_of_disjoint_ker le_rfl R.avoids_kernel

theorem RainbowDomainLine.actual_projective_edge (R : RainbowDomainLine Φ U)
    (hU : ∀i,U i≠0) (hf : ∀i j (c : ℂ),U i=c • U j→i=j) :
    (projectiveGraph U).Adj (matrixPoint U hU R.first) (matrixPoint U hU R.second) := by
  refine ⟨fun he => R.first_ne_second (matrixPoint_injective U hU hf he),
    Submodule.span ℂ ({U R.first,U R.second} : Set Mat),R.domain_dimension hU hf,?_,?_,?_⟩
  · rw [R.intersection_card]
  · apply (Submodule.mk_mem_projectivization_iff _ _).mpr
    exact Submodule.subset_span (by simp)
  · apply (Submodule.mk_mem_projectivization_iff _ _).mpr
    exact Submodule.subset_span (by simp)

/-- The projective rich line itself is disjoint from the projectivized kernel,
including points outside the finite Platonic configuration. -/
theorem RainbowDomainLine.projective_kernel_avoiding (R : RainbowDomainLine Φ U)
    (z : DomainPoint)
    (hz : z∈(Submodule.span ℂ ({U R.first,U R.second} : Set Mat)).projectivization) :
    z∉Φ.ker.projectivization := by
  induction z using Projectivization.ind with
  | h v hv =>
    intro hk
    apply hv
    exact Submodule.disjoint_def.mp R.avoids_kernel v
      ((Submodule.mk_mem_projectivization_iff _ hv).mp hz)
      ((Submodule.mk_mem_projectivization_iff _ hv).mp hk)

theorem mixed_cards_rank_ge_two (hmix : MixedCards Φ U) : 2≤Module.finrank ℂ Φ.range := by
  obtain ⟨i,j,D,E,hDE⟩ := hmix
  exact rank_ge_two_of_nonproportional Φ (U i) (U j) D.nonzero E.nonzero (D.not_proportional E hDE)

/-- The source first conclusion of A.24 does not need the rank upper bound:
two different actual matchings already imply the kernel bound used by A.20. -/
theorem platonic_mixed_rainbow (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat)
    (Φ : Mat→ₗ[ℂ]Tensor ℂ P)
    (hcards : ∀i,Φ (e (representative g i))=0 ∨
      Nonempty (NonsingularCard (Φ (e (representative g i)))))
    (hmix : MixedCards Φ (fun i => e (representative g i))) :
    Nonempty (RainbowDomainLine Φ (fun i => e (representative g i))) :=
  platonic_rainbow_domain_line g e Φ (mixed_cards_rank_ge_two hmix) hcards hmix

/-- The full actual-domain geometric dichotomy in 9.11. The first branch is
only the fixed-matching condition, not yet its proper-factor reconstruction. -/
theorem platonic_ruling_or_rainbow (g : PlatonicModel) (e : Mat≃ₗ[ℂ]Mat)
    (Φ : Mat→ₗ[ℂ]Tensor ℂ P) (hr : 2≤Module.finrank ℂ Φ.range)
    (hcards : ∀i,Φ (e (representative g i))=0 ∨
      Nonempty (NonsingularCard (Φ (e (representative g i))))) :
    (∃m : Equiv.Perm P,∀i,∀C : NonsingularCard (Φ (e (representative g i))),C.matching=m) ∨
    Nonempty (RainbowDomainLine Φ (fun i => e (representative g i))) := by
  classical
  by_cases hm : MixedCards Φ (fun i => e (representative g i))
  · exact Or.inr (platonic_rainbow_domain_line g e Φ hr hcards hm)
  have hc := transformed_kernel_deleted_connected g e Φ.ker (kernel_dimension_le_two Φ hr)
  obtain ⟨i⟩ := hc.nonempty
  have hi : Φ (e (representative g i.val))≠0 := by
    simpa only [Set.mem_setOf_eq,LinearMap.mem_ker] using i.property
  obtain ⟨C⟩ := (hcards i.val).resolve_left hi
  refine Or.inl ⟨C.matching,?_⟩
  intro j E
  by_contra he
  exact hm ⟨j,i.val,E,C,he⟩

end Holant.Platonic.RankDeficientLocalization
