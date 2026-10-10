import Holant.Certificates.TetrahedralPreservers.FullRankNormalForms
import Holant.Certificates.PlatonicIncidence.Subspaces

/-! Range geometry for arbitrary maps. Root bases are extracted from the
actual range; no finite atlas of linear maps is assumed. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.PlatonicIncidence
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

def rootIndices (W : Submodule ℂ V) : Finset (Fin 12) := by
  classical
  exact Finset.univ.filter fun i => standardPoint i ∈ W

@[simp] theorem mem_rootIndices (W : Submodule ℂ V) (i : Fin 12) :
    i ∈ rootIndices W ↔ standardPoint i ∈ W := by
  classical
  simp [rootIndices]

theorem span_root_range (A : End) (hA : OneSided Standard A) :
    Submodule.span ℂ (Set.range (fun i : {i : Fin 12 // standardPoint i ∈ LinearMap.range A.mulVecLin} =>
      standardPoint i.val)) = LinearMap.range A.mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact i.property
  · conv_lhs => rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    have hh := hA _ (standard_axis j)
    rw [Matrix.mulVec_single_one] at hh
    rcases hh with hz | hm
    · rw [hz]
      exact Submodule.zero_mem _
    · obtain ⟨k,c,hc,he⟩ := (standard_iff _).mp hm
      have hk : standardPoint k ∈ LinearMap.range A.mulVecLin := by
        refine ⟨c⁻¹ • Pi.single j 1,?_⟩
        change A *ᵥ (c⁻¹ • Pi.single j 1)=standardPoint k
        rw [Matrix.mulVec_smul,Matrix.mulVec_single_one,he,smul_smul,inv_mul_cancel₀ hc,one_smul]
      rw [he]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨k,hk⟩,rfl⟩

/-- A basis consisting of genuine root directions is extracted from the range. -/
theorem range_root_basis (A : End) (hA : OneSided Standard A) {r : ℕ} (hr : A.rank=r) :
    ∃ u : Fin r → Fin 12, LinearIndependent ℂ (fun i => standardPoint (u i)) ∧
      (∀ i, standardPoint (u i) ∈ LinearMap.range A.mulVecLin) ∧
      Submodule.span ℂ (Set.range (fun i => standardPoint (u i))) = LinearMap.range A.mulVecLin := by
  classical
  let D := {i : Fin 12 // standardPoint i ∈ LinearMap.range A.mulVecLin}
  let v : D → V := fun i => standardPoint i.val
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' ℂ v
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hli,hspan]
    change Module.finrank ℂ (Submodule.span ℂ (Set.range v))=r
    rw [show Submodule.span ℂ (Set.range v)=LinearMap.range A.mulVecLin from span_root_range A hA]
    exact hr
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (a (e i)).val,?_,fun i => (a (e i)).property,?_⟩
  · exact hli.comp e e.injective
  · have he : Set.range (fun i : Fin r => standardPoint (a (e i)).val) = Set.range (v ∘ a) := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩; exact ⟨e i,rfl⟩
      · rintro ⟨i,rfl⟩
        obtain ⟨j,rfl⟩ := e.surjective i
        exact ⟨j,rfl⟩
    rw [he,hspan]
    exact span_root_range A hA

theorem rank_sharp (A : End) : (sharp A).rank=A.rank := by
  have hJ : J.det ≠ 0 := by
    have hh := congrArg Matrix.det J_square
    simp only [Matrix.det_mul,Matrix.det_one] at hh
    intro hz
    simp [hz] at hh
  rw [sharp,Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hJ,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hJ,Matrix.rank_transpose]

theorem pairing_symm (u v : V) : pairing u v=pairing v u := by
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairing_smul_left (c : ℂ) (u v : V) : pairing (c • u) v=c*pairing u v := by
  simp [pairing,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairing_range_scale {A : End} {u r s : V} (hu : u ∈ LinearMap.range (sharp A).mulVecLin)
    {c : ℂ} (h : A *ᵥ r=c • (A *ᵥ s)) : pairing u r=c*pairing u s := by
  obtain ⟨v,hv⟩ := hu
  change sharp A *ᵥ v=u at hv
  rw [← hv,pairing_symm (sharp A *ᵥ v) r,← pairing_adjoint,h,pairing_smul_left,
    pairing_adjoint,pairing_symm s]

theorem pairing_range_cross_zero {A : End} {u v r s : V}
    (hu : u ∈ LinearMap.range (sharp A).mulVecLin) (hv : v ∈ LinearMap.range (sharp A).mulVecLin)
    {c : ℂ} (h : A *ᵥ r=c • (A *ᵥ s)) :
    pairing u r*pairing v s-pairing u s*pairing v r=0 := by
  rw [pairing_range_scale hu h,pairing_range_scale hv h]
  ring

/-- Distinct projected root points force distinct nonzero image directions. -/
theorem projected_directions_bound (A : End) (hA : OneSided Standard A)
    {n m : ℕ} (hm : 2 ≤ m) (u : Fin n → V)
    (hu : ∀ i, u i ∈ LinearMap.range (sharp A).mulVecLin) (w : Fin m → Fin 12)
    (hw : ∀ a b : Fin m, a ≠ b → ∃ i j : Fin n,
      pairing (u i) (standardPoint (w a))*pairing (u j) (standardPoint (w b))-
        pairing (u i) (standardPoint (w b))*pairing (u j) (standardPoint (w a)) ≠ 0) :
    m ≤ (rootIndices (LinearMap.range A.mulVecLin)).card := by
  classical
  letI : NeZero m := ⟨by omega⟩
  have hn (a : Fin m) : A *ᵥ standardPoint (w a) ≠ 0 := by
    have hb : ∃ b : Fin m, a ≠ b := by
      by_cases ha : a=0
      · refine ⟨⟨1,by omega⟩,?_⟩
        subst a
        simp
      · exact ⟨0,ha⟩
    obtain ⟨b,hab⟩ := hb
    obtain ⟨i,j,hij⟩ := hw a b hab
    intro hz
    apply hij
    exact pairing_range_cross_zero (hu i) (hu j) (c:=0) (by simp [hz])
  have hc (a : Fin m) : ∃ k : Fin 12, ∃ c : ℂ, c ≠ 0 ∧
      A *ᵥ standardPoint (w a)=c • standardPoint k :=
    (standard_iff _).mp ((hA _ (standardPoint_mem _)).resolve_left (hn a))
  choose k c hc he using hc
  have hi : Function.Injective k := by
    intro a b hab
    by_contra hn
    obtain ⟨i,j,hij⟩ := hw a b hn
    apply hij
    apply pairing_range_cross_zero (hu i) (hu j) (c:=c a*(c b)⁻¹)
    rw [he a,he b,hab,smul_smul]
    congr 1
    field_simp [hc b]
  have hk (a : Fin m) : standardPoint (k a) ∈ LinearMap.range A.mulVecLin := by
    refine ⟨(c a)⁻¹ • standardPoint (w a),?_⟩
    change A *ᵥ ((c a)⁻¹ • standardPoint (w a))=standardPoint (k a)
    rw [Matrix.mulVec_smul,he a,smul_smul,inv_mul_cancel₀ (hc a),one_smul]
  let f : Fin m → ↑(rootIndices (LinearMap.range A.mulVecLin)) :=
    fun a => ⟨k a,(mem_rootIndices _ _).mpr (hk a)⟩
  have hf : Function.Injective f := fun a b hh => hi (congrArg Subtype.val hh)
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem rootIndices_two_dimensional_bound (W : Submodule ℂ V) (hW : Module.finrank ℂ W ≤ 2) :
    (rootIndices W).card ≤ 3 := by
  let W' : Submodule ℂ PlatonicIncidence.Mat := W.map coordinates.symm.toLinearMap
  have hdim : Module.finrank ℂ W' ≤ 2 := by
    have he := (Submodule.equivMapOfInjective coordinates.symm.toLinearMap coordinates.symm.injective W).finrank_eq
    exact he ▸ hW
  have hset : rootIndices W=deletion .tetrahedral W' := by
    ext i
    rw [mem_rootIndices,mem_deletion]
    constructor
    · intro hi
      refine ⟨standardPoint i,hi,?_⟩
      exact coordinates.symm_apply_apply _
    · rintro ⟨r,hr,he⟩
      have hh := congrArg coordinates he
      change coordinates (coordinates.symm r)=standardPoint i at hh
      rw [coordinates.apply_symm_apply] at hh
      exact hh ▸ hr
  rw [hset]
  exact deletion_bound .tetrahedral W' hdim

end Holant.Certificates.TetrahedralPreservers
