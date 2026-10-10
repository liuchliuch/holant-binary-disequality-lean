import Holant.Certificates.TetrahedralPreservers.Frobenius
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Arbitrary complex rank-one maps, not just an enumerated candidate family. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.PlatonicIncidence
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- u v^T J: the rank-one operator defined by the actual bilinear form. -/
def outer (u v : V) : End := fun i j => u i * frobeniusSigns j * v j

theorem outer_apply (u v r : V) : outer u v *ᵥ r = pairing v r • u := by
  ext i
  simp [outer,Matrix.mulVec,dotProduct,pairing,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

@[simp] theorem sharp_outer (u v : V) : sharp (outer u v) = outer v u := by
  ext i j
  rw [sharp_apply]
  simp only [outer]
  calc
    frobeniusSigns i * (u j * frobeniusSigns i * v i) * frobeniusSigns j =
      (frobeniusSigns i * frobeniusSigns i) * (v i * frobeniusSigns j * u j) := by ring
    _ = _ := by rw [signs_square,one_mul]

theorem outer_ne_zero {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) : outer u v ≠ 0 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hv
  have hs : frobeniusSigns j ≠ 0 := by
    intro h
    have := signs_square j
    simp [h] at this
  intro h
  exact (mul_ne_zero (mul_ne_zero hi hs) hj) (congrFun (congrFun h i) j)

theorem pairing_axis (v : V) (i : Fin 4) :
    pairing v (Pi.single i 1) = frobeniusSigns i * v i := by
  simp [pairing,Pi.single_apply]

theorem pairing_nonzero {v : V} (hv : v ≠ 0) : ∃ r : V, pairing v r ≠ 0 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  refine ⟨Pi.single i 1,?_⟩
  rw [pairing_axis]
  apply mul_ne_zero _ hi
  intro h
  have := signs_square i
  simp [h] at this

theorem range_outer {u v : V} (hv : v ≠ 0) :
    LinearMap.range (outer u v).mulVecLin = Submodule.span ℂ {u} := by
  apply le_antisymm
  · rintro y ⟨r,rfl⟩
    change outer u v *ᵥ r ∈ _
    rw [outer_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · rw [Submodule.span_le,Set.singleton_subset_iff]
    obtain ⟨r,hr⟩ := pairing_nonzero hv
    refine ⟨(pairing v r)⁻¹ • r,?_⟩
    change outer u v *ᵥ ((pairing v r)⁻¹ • r) = u
    rw [Matrix.mulVec_smul,outer_apply,smul_smul,inv_mul_cancel₀ hr,one_smul]

theorem rank_outer {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) :
    (outer u v).rank = 1 := by
  rw [Matrix.rank,range_outer hv]
  exact finrank_span_singleton hu

/-- Every complex matrix of actual linear-map rank one has a Frobenius outer form. -/
theorem rank_one_iff (A : End) : A.rank = 1 ↔
    ∃ u v : V, u ≠ 0 ∧ v ≠ 0 ∧ A = outer u v := by
  constructor
  · intro hA
    have hAn : A ≠ 0 := by intro h; simpa [h] using hA
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hAn
    obtain ⟨j,hij⟩ := Function.ne_iff.mp hi
    let u : V := fun k => A k j
    have hu : u ≠ 0 := fun h => hij (congrFun h i)
    have huR : u ∈ LinearMap.range A.mulVecLin := by
      exact ⟨Pi.single j 1,Matrix.mulVec_single_one A j⟩
    have hR : LinearMap.range A.mulVecLin = Submodule.span ℂ {u} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hA huR hu
    have hcols (k : Fin 4) : ∃ c : ℂ, c • u = fun a => A a k := by
      apply Submodule.mem_span_singleton.mp
      rw [← hR]
      exact ⟨Pi.single k 1,Matrix.mulVec_single_one A k⟩
    choose c hc using hcols
    let v : V := fun k => frobeniusSigns k * c k
    have he : A = outer u v := by
      ext a k
      have h := congrFun (hc k) a
      change c k * u a = A a k at h
      rw [← h]
      change c k * u a = u a * frobeniusSigns k * (frobeniusSigns k * c k)
      calc
        _ = u a * (frobeniusSigns k * frobeniusSigns k) * c k := by rw [signs_square]; ring
        _ = _ := by ring
    refine ⟨u,v,hu,?_,he⟩
    intro hv
    apply hAn
    rw [he,hv]
    ext a b
    simp [outer]
  · rintro ⟨u,v,hu,hv,rfl⟩
    exact rank_outer hu hv

/-- The set detects every nonzero linear functional, equivalently spans V. -/
def Detects (S : Set V) : Prop :=
  ∀ v : V, v ≠ 0 → ∃ r ∈ S, pairing v r ≠ 0

theorem oneSided_outer {S : Set V} (hS : Saturated S) {u v : V} (hu : u ∈ S) :
    OneSided S (outer u v) := by
  intro r hr
  rw [outer_apply]
  by_cases h : pairing v r = 0
  · simp [h]
  · exact Or.inr (hS hu h)

theorem twoSided_outer {S : Set V} (hS : Saturated S) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) : TwoSided S (outer u v) := by
  exact ⟨oneSided_outer hS hu,by rw [sharp_outer]; exact oneSided_outer hS hv⟩

theorem outer_left_mem {S : Set V} (hS : Saturated S) (hD : Detects S)
    {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (h : OneSided S (outer u v)) : u ∈ S := by
  obtain ⟨r,hr,hn⟩ := hD v hv
  rcases h r hr with hh | hh
  · rw [outer_apply] at hh
    exact False.elim ((smul_ne_zero hn hu) hh)
  · rw [outer_apply] at hh
    have := hS hh (inv_ne_zero hn)
    simpa [smul_smul,hn] using this

/-- Completeness for rank one uses arbitrary complex input matrices. -/
theorem rank_one_twoSided_iff {S : Set V} (hS : Saturated S) (hD : Detects S)
    (A : End) (hA : A.rank = 1) : TwoSided S A ↔
      ∃ u v : V, u ∈ S ∧ v ∈ S ∧ A = outer u v := by
  constructor
  · intro h
    obtain ⟨u,v,hu,hv,rfl⟩ := (rank_one_iff A).mp hA
    exact ⟨u,v,outer_left_mem hS hD hu hv h.1,
      outer_left_mem hS hD hv hu (by simpa using h.2),rfl⟩
  · rintro ⟨u,v,hu,hv,rfl⟩
    exact twoSided_outer hS hu hv

end Holant.Certificates.TetrahedralPreservers
