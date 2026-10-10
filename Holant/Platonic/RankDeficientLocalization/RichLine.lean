import Holant.Platonic.RankDeficientLocalization.LinearGeometry

/-! A matching-changing edge in the actual kernel-deleted domain produces an
exactly three-point, kernel-avoiding rainbow line. Matching labels are recovered
from literal nonsingular card presentations; no colouring is supplied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Platonic.RankDeficientLocalization
open Holant Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Certificates.MatchingContractionClosure Holant.Platonic.RainbowLocalization
variable {P : Type*} [Fintype P] [DecidableEq P] {n : ℕ}

structure NonsingularCard (F : Tensor ℂ P) where
  presentation : Presentation ℂ P
  det_ne_zero : ∀e,(presentation.matrix e).det≠0
  scalar_ne_zero : presentation.scalar≠0
  value : F=presentation.tensor

theorem NonsingularCard.nonzero {F : Tensor ℂ P} (D : NonsingularCard F) : F≠0 := by
  rw [D.value]
  exact productValue_nonzero _ _ _ D.det_ne_zero D.scalar_ne_zero

def NonsingularCard.matching {F : Tensor ℂ P} (D : NonsingularCard F) : Equiv.Perm P :=
  (presentationMatching D.presentation).mate

theorem NonsingularCard.matching_eq {F : Tensor ℂ P} (D E : NonsingularCard F) :
    D.matching=E.matching := by
  apply matching_eq_of_tensor_smul D.presentation E.presentation D.det_ne_zero E.det_ne_zero
    D.scalar_ne_zero E.scalar_ne_zero 1
  simpa only [one_smul] using D.value.symm.trans E.value

theorem NonsingularCard.not_proportional {F H : Tensor ℂ P}
    (D : NonsingularCard F) (E : NonsingularCard H) (hne : D.matching≠E.matching) :
    ¬ Proportional F H := by
  rintro ⟨c,hc,he⟩
  rw [D.value,E.value] at he
  exact hne (matching_eq_of_tensor_smul D.presentation E.presentation D.det_ne_zero E.det_ne_zero
    D.scalar_ne_zero E.scalar_ne_zero c he)

def MixedCards (Φ : Mat →ₗ[ℂ] Tensor ℂ P) (U : Fin n→Mat) : Prop :=
  ∃i j,∃D : NonsingularCard (Φ (U i)),∃E : NonsingularCard (Φ (U j)),D.matching≠E.matching

/-- The entire actual domain intersection is exactly the three selected
points, and the whole vector line is disjoint from the complex kernel. -/
structure RainbowDomainLine (Φ : Mat →ₗ[ℂ] Tensor ℂ P) (U : Fin n→Mat) where
  first : Fin n
  second : Fin n
  third : Fin n
  first_ne_second : first≠second
  third_ne_first : third≠first
  third_ne_second : third≠second
  card₀ : NonsingularCard (Φ (U first))
  card₁ : NonsingularCard (Φ (U second))
  card₂ : NonsingularCard (Φ (U third))
  different₀₁ : card₀.matching≠card₁.matching
  different₂₀ : card₂.matching≠card₀.matching
  different₂₁ : card₂.matching≠card₁.matching
  third_mem : U third∈Submodule.span ℂ ({U first,U second} : Set Mat)
  exact_points : matrixIntersection U (Submodule.span ℂ ({U first,U second} : Set Mat))=
    {first,second,third}
  avoids_kernel : Disjoint (Submodule.span ℂ ({U first,U second} : Set Mat)) Φ.ker

/-- Generic edge lemma: the entire actual rich secant, not an assumed
three-element subgraph, is proved to consist of exactly the rainbow triple. -/
theorem rainbow_of_changed_edge (Φ : Mat →ₗ[ℂ] Tensor ℂ P) (U : Fin n→Mat)
    (hU : ∀i,U i≠0) (hf : ∀i j (c : ℂ),U i=c • U j→i=j)
    (hcards : ∀i,Φ (U i)=0 ∨ Nonempty (NonsingularCard (Φ (U i))))
    (i j : Fin n) (ha : (matrixGraph U).Adj i j)
    (D : NonsingularCard (Φ (U i))) (E : NonsingularCard (Φ (U j)))
    (hne : D.matching≠E.matching) : Nonempty (RainbowDomainLine Φ U) := by
  classical
  let L := Submodule.span ℂ ({U i,U j} : Set Mat)
  let S := matrixIntersection U L
  have hi : U i∈L := Submodule.subset_span (by simp)
  have hj : U j∈L := Submodule.subset_span (by simp)
  have hinj : Set.InjOn Φ L := span_pair_injOn Φ (U i) (U j) D.nonzero E.nonzero
    (D.not_proportional E hne)
  have hdis : Disjoint L Φ.ker := span_pair_disjoint_kernel Φ (U i) (U j)
    D.nonzero E.nonzero (D.not_proportional E hne)
  have hnonzero (k : Fin n) (hk : U k∈L) : Φ (U k)≠0 := by
    intro hz
    exact hU k (hinj hk L.zero_mem (by simpa using hz))
  have hrich : 3≤S.card := matrix_adj_rich_pair U hU hf i j ha
  obtain ⟨k,hk,hkne⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({i,j} : Finset (Fin n)).card<S.card from lt_of_le_of_lt Finset.card_le_two (by omega))
  have hkL : U k∈L := (mem_matrixIntersection U L k).mp hk
  have hks : k≠i ∧ k≠j := by simpa using hkne
  have hki : k≠i := hks.1
  have hkj : k≠j := hks.2
  obtain ⟨F⟩ := (hcards k).resolve_left (hnonzero k hkL)
  have himage (a : Fin n) (haL : U a∈L) :
      Φ (U a)∈Submodule.span ℂ ({D.presentation.tensor,E.presentation.tensor} : Set (Tensor ℂ P)) := by
    obtain ⟨x,y,he⟩ := Submodule.mem_span_pair.mp haL
    apply Submodule.mem_span_pair.mpr
    refine ⟨x,y,?_⟩
    rw [←D.value,←E.value,←map_smul,←map_smul,←map_add,he]
  have hpull (a b : Fin n) (haL : U a∈L) (hbL : U b∈L)
      (h : Proportional (Φ (U a)) (Φ (U b))) : a=b := by
    obtain ⟨c,hc,he⟩ := h
    apply hf a b c
    apply hinj haL (L.smul_mem c hbL)
    simpa only [map_smul] using he
  have hFline : F.presentation.tensor∈Submodule.span ℂ
      ({D.presentation.tensor,E.presentation.tensor} : Set (Tensor ℂ P)) := by
    rw [←F.value]
    exact himage k hkL
  have hFD : F.matching≠D.matching := by
    intro hm
    have hh := same_matching_on_line_proportional F.presentation D.presentation E.presentation
      F.det_ne_zero D.det_ne_zero E.det_ne_zero F.scalar_ne_zero D.scalar_ne_zero E.scalar_ne_zero
      hm hne hFline
    rw [←F.value,←D.value] at hh
    exact hki (hpull k i hkL hi hh)
  have hFE : F.matching≠E.matching := by
    intro hm
    have hh := same_matching_on_line_proportional F.presentation E.presentation D.presentation
      F.det_ne_zero E.det_ne_zero D.det_ne_zero F.scalar_ne_zero E.scalar_ne_zero D.scalar_ne_zero
      hm hne.symm (by simpa only [Set.pair_comm E.presentation.tensor D.presentation.tensor] using hFline)
    rw [←F.value,←E.value] at hh
    exact hkj (hpull k j hkL hj hh)
  have hexact : S={i,j,k} := by
    apply Finset.ext
    intro a
    constructor
    · intro haS
      have haL := (mem_matrixIntersection U L a).mp haS
      obtain ⟨A⟩ := (hcards a).resolve_left (hnonzero a haL)
      have hh := matching_point_on_rainbow_line D.presentation E.presentation F.presentation A.presentation
        D.det_ne_zero E.det_ne_zero F.det_ne_zero A.det_ne_zero
        D.scalar_ne_zero E.scalar_ne_zero F.scalar_ne_zero A.scalar_ne_zero hne hFD hFE hFline
        (by rw [←A.value]; exact himage a haL)
      rw [←D.value,←E.value,←F.value,←A.value] at hh
      rcases hh with hh|hh|hh
      · simp [hpull a i haL hi hh]
      · simp [hpull a j haL hj hh]
      · simp [hpull a k haL hkL hh]
    · intro haS
      simp only [Finset.mem_insert,Finset.mem_singleton] at haS
      rcases haS with rfl|rfl|rfl
      · exact (mem_matrixIntersection U L _).mpr hi
      · exact (mem_matrixIntersection U L _).mpr hj
      · exact hk
  exact ⟨⟨i,j,k,ha.1,hki,hkj,D,E,F,hne,hFD,hFE,hkL,hexact,hdis⟩⟩

/-- The source graph is the actual complete rich-line graph after deleting
exactly the kernel points. The presentation-based labels are constructed here. -/
theorem rainbow_of_deleted_connected (Φ : Mat →ₗ[ℂ] Tensor ℂ P) (U : Fin n→Mat)
    (hU : ∀i,U i≠0) (hf : ∀i j (c : ℂ),U i=c • U j→i=j)
    (hcards : ∀i,Φ (U i)=0 ∨ Nonempty (NonsingularCard (Φ (U i))))
    (hc : ((matrixGraph U).induce {i | U i∉Φ.ker}).Connected)
    (hmix : MixedCards Φ U) : Nonempty (RainbowDomainLine Φ U) := by
  classical
  let V := {i : Fin n // U i∉Φ.ker}
  have hex (i : V) : Nonempty (NonsingularCard (Φ (U i.val))) :=
    (hcards i.val).resolve_left (by simpa only [LinearMap.mem_ker] using i.property)
  let cards (i : V) := Classical.choice (hex i)
  obtain ⟨i,j,D,E,hDE⟩ := hmix
  let a : V := ⟨i,by simpa only [LinearMap.mem_ker] using D.nonzero⟩
  let b : V := ⟨j,by simpa only [LinearMap.mem_ker] using E.nonzero⟩
  have hne : (cards a).matching≠(cards b).matching := by
    rw [(cards a).matching_eq D,(cards b).matching_eq E]
    exact hDE
  obtain ⟨x,y,hxy,hcxy⟩ := connected_exists_changed_edge _ hc (fun i : V => (cards i).matching) a b hne
  exact rainbow_of_changed_edge Φ U hU hf hcards x.val y.val hxy (cards x) (cards y) hcxy

/-- A.24 and 9.11's exact kernel-deleted rich-line argument, for every
standard or analytically transported actual Platonic domain configuration. -/
theorem platonic_rainbow_domain_line (g : PlatonicModel) (e : Mat ≃ₗ[ℂ] Mat)
    (Φ : Mat →ₗ[ℂ] Tensor ℂ P) (hr : 2≤Module.finrank ℂ Φ.range)
    (hcards : ∀i,Φ (e (representative g i))=0 ∨
      Nonempty (NonsingularCard (Φ (e (representative g i)))))
    (hmix : MixedCards Φ (fun i => e (representative g i))) :
    Nonempty (RainbowDomainLine Φ (fun i => e (representative g i))) :=
  rainbow_of_deleted_connected Φ _ (transformed_representative_nonzero g e)
    (transformed_representative_faithful g e) hcards
    (transformed_kernel_deleted_connected g e Φ.ker (kernel_dimension_le_two Φ hr)) hmix

end Holant.Platonic.RankDeficientLocalization
