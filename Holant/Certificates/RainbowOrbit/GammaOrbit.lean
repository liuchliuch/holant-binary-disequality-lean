import Holant.Certificates.RainbowOrbit.DeckPermutations
import Mathlib.Algebra.Group.Submonoid.Membership

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

def wordPermutation {ι X : Type*} (generators : ι→Equiv.Perm X) : List ι→Equiv.Perm X
  | [] => 1
  | o::w => wordPermutation generators w*generators o

theorem wordPermutation_append {ι X : Type*} (gen : ι→Equiv.Perm X) (v w : List ι) :
    wordPermutation gen (v++w)=wordPermutation gen w*wordPermutation gen v := by
  induction v with
  | nil => simp [wordPermutation]
  | cons o v ih => simp only [List.cons_append,wordPermutation,ih,mul_assoc]

/-- Positive words already exhaust the generated group on a finite deck. -/
theorem gamma_mem_iff_word {ι X : Type*} [Finite X] (gen : ι→Equiv.Perm X) (γ : Equiv.Perm X) :
    γ∈Subgroup.closure (Set.range gen) ↔ ∃w : List ι,wordPermutation gen w=γ := by
  constructor
  · intro hγ
    have hm : γ∈Submonoid.closure (Set.range gen) := by
      rw [←Subgroup.closure_toSubmonoid_of_finite]
      exact hγ
    clear hγ
    induction hm using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact ⟨[i],by simp [wordPermutation]⟩
    | one => exact ⟨[],rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨v,rfl⟩ := ihx
      obtain ⟨w,rfl⟩ := ihy
      exact ⟨w++v,wordPermutation_append gen w v⟩
  · rintro ⟨w,rfl⟩
    induction w with
    | nil => exact (Subgroup.closure _).one_mem
    | cons o w ih => exact (Subgroup.closure _).mul_mem ih (Subgroup.subset_closure ⟨o,rfl⟩)

theorem restricted_word_apply {n : ℕ} (D : Finset Point) (R : Fin n→BinaryMatrix)
    (hd : ∀i,(R i).det≠0) (gen : Operation n→Equiv.Perm {p : Point // p∈D})
    (hgen : ∀o p,(gen o p).val=operationPoint R hd o p.val) (w : List (Operation n))
    (p : {p : Point // p∈D}) :
    (wordPermutation gen w p).val=runPointWord R hd w p.val := by
  induction w generalizing p with
  | nil => rfl
  | cons o w ih =>
    simp only [wordPermutation,Equiv.Perm.mul_apply,runPointWord]
    rw [ih,hgen]

def GammaOrbit {n : ℕ} (D : Finset Point)
    (gen : Operation n→Equiv.Perm {p : Point // p∈D}) (S₀ S : Finset Point) : Prop := by
  classical
  exact ∃γ : Equiv.Perm {p : Point // p∈D},γ∈Subgroup.closure (Set.range gen) ∧
    S₀.map (Equiv.Perm.ofSubtype γ).toEmbedding=S

theorem gammaOrbit_iff_word {n : ℕ} (D : Finset Point) (R : Fin n→BinaryMatrix)
    (hd : ∀i,(R i).det≠0) (gen : Operation n→Equiv.Perm {p : Point // p∈D})
    (hgen : ∀o p,(gen o p).val=operationPoint R hd o p.val)
    (S₀ S : Finset Point) (hS₀ : S₀⊆D) :
    GammaOrbit D gen S₀ S ↔ ∃w : List (Operation n),runWord R hd w S₀=S := by
  classical
  have he (w : List (Operation n)) :
      S₀.map (Equiv.Perm.ofSubtype (wordPermutation gen w)).toEmbedding=runWord R hd w S₀ := by
    ext p
    simp only [runWord,Finset.mem_map]
    constructor
    · rintro ⟨q,hq,hqp⟩
      refine ⟨q,hq,?_⟩
      change runPointWord R hd w q=p
      rw [←restricted_word_apply D R hd gen hgen w ⟨q,hS₀ hq⟩]
      simpa only [Equiv.toEmbedding_apply,Equiv.Perm.ofSubtype_apply_of_mem _ (hS₀ hq)] using hqp
    · rintro ⟨q,hq,hqp⟩
      refine ⟨q,hq,?_⟩
      change Equiv.Perm.ofSubtype (wordPermutation gen w) q=p
      rw [Equiv.Perm.ofSubtype_apply_of_mem _ (hS₀ hq),restricted_word_apply D R hd gen hgen]
      exact hqp
  constructor
  · rintro ⟨γ,hγ,hS⟩
    obtain ⟨w,rfl⟩ := (gamma_mem_iff_word gen γ).mp hγ
    exact ⟨w,(he w).symm.trans hS⟩
  · rintro ⟨w,hw⟩
    exact ⟨wordPermutation gen w,(gamma_mem_iff_word gen _).mpr ⟨w,rfl⟩,(he w).trans hw⟩

theorem baseLine_subset_deck (g : PlatonicModel) : baseLine⊆deck g := by
  classical
  intro p hp
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hp
  exact (standard_deck_semantics g _).mp ⟨r,base r,base_nonzero r,base_inMatching g r,rfl⟩

theorem standard_gamma_orbit_iff (g : PlatonicModel) (S : Finset Point) :
    GammaOrbit (deck g) (standardOperationPermutation g) baseLine S ↔ RainbowLine g S := by
  rw [gammaOrbit_iff_word (deck g) (representative g) (representative_det_ne_zero g)
    (standardOperationPermutation g) (by intros; rfl) baseLine S (baseLine_subset_deck g)]
  exact generatedOrbit_iff_rainbowLine g S

theorem standard_gamma_orbit_card (g : PlatonicModel) :
    {S : Finset Point | GammaOrbit (deck g) (standardOperationPermutation g) baseLine S}.ncard=(size g)^3 := by
  have he : {S : Finset Point | GammaOrbit (deck g) (standardOperationPermutation g) baseLine S}=
      {S : Finset Point | RainbowLine g S} := by ext S; exact standard_gamma_orbit_iff g S
  rw [he,all_rainbow_lines_card]

theorem markedBaseLine_subset_deck (f : Form) : markedBaseLine f⊆markedDeck f := by
  classical
  intro p hp
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hp
  exact (markedDeck_iff_mem f _).mp ⟨r,markedInitial f r,markedInitial_nonzero f r,
    matching_mark_forward f r (base r) (base_inMatching .octahedral r),rfl⟩

theorem marked_gamma_orbit_iff (f : Form) (S : Finset Point) :
    GammaOrbit (markedDeck f) (markedOperationPermutation f) (markedBaseLine f) S ↔ MarkedRainbowLine f S := by
  rw [gammaOrbit_iff_word (markedDeck f) (markedRepresentative f) (markedRepresentative_det f)
    (markedOperationPermutation f) (by intros; rfl) (markedBaseLine f) S (markedBaseLine_subset_deck f)]
  exact marked_generatedOrbit_iff_rainbowLine f S

theorem marked_gamma_orbit_card (f : Form) :
    {S : Finset Point | GammaOrbit (markedDeck f) (markedOperationPermutation f) (markedBaseLine f) S}.ncard=13824 := by
  have he : {S : Finset Point | GammaOrbit (markedDeck f) (markedOperationPermutation f) (markedBaseLine f) S}=
      {S : Finset Point | MarkedRainbowLine f S} := by ext S; exact marked_gamma_orbit_iff f S
  rw [he,marked_all_lines_card]

end
end Holant.Certificates.RainbowOrbit
