import Holant.Platonic.FixedMatchingRuling.SegreRuling
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Generic Segre equations and rulings in the actual finite tensor product. -/
noncomputable section
namespace Holant.Platonic.FixedMatchingRuling.Segre
open scoped BigOperators
open Function Module
variable {M : Type*} [Fintype M] {κ : M → Type*}
variable {W : M → Type*} [∀ e, AddCommGroup (W e)] [∀ e, Module ℂ (W e)]

/-- The full tensor-product basis equivalence; factor dimensions may differ. -/
def tensorCoordinates [∀ e, Fintype (κ e)] (b : ∀ e, Basis (κ e) ℂ (W e)) :
    PiTensorProduct ℂ W ≃ₗ[ℂ] Array κ := (Basis.piTensorProduct b).equivFun

@[simp] theorem tensorCoordinates_tprod [∀ e, Fintype (κ e)]
    (b : ∀ e, Basis (κ e) ℂ (W e)) (U : ∀ e, W e) :
    tensorCoordinates b (PiTensorProduct.tprod ℂ U) =
      product (fun e => (b e).equivFun (U e)) := by
  funext x
  simp [tensorCoordinates, Basis.equivFun_apply, product]

/-- The affine Segre cone in the actual tensor space, including zero. -/
def TensorPureOrZero (t : PiTensorProduct ℂ W) : Prop :=
  t = 0 ∨ ∃ U : ∀ e, W e, t = PiTensorProduct.tprod ℂ U

theorem tensorPureOrZero_coordinates [∀ e, Fintype (κ e)]
    (b : ∀ e, Basis (κ e) ℂ (W e)) (t : PiTensorProduct ℂ W) :
    TensorPureOrZero t ↔ IsPureOrZero (tensorCoordinates b t) := by
  constructor
  · rintro (rfl | ⟨U, rfl⟩)
    · exact Or.inl (map_zero _)
    · exact Or.inr ⟨fun e => (b e).equivFun (U e), tensorCoordinates_tprod b U⟩
  · rintro (hz | ⟨U, hU⟩)
    · left
      exact (tensorCoordinates b).injective (by simpa using hz)
    · right
      refine ⟨fun e => (b e).equivFun.symm (U e), ?_⟩
      apply (tensorCoordinates b).injective
      rw [hU, tensorCoordinates_tprod]
      simp only [LinearEquiv.apply_symm_apply]

/-- Every one-factor flattening minor is sufficient and necessary for the
actual tensor-product affine Segre cone. -/
theorem tensor_minors_iff [DecidableEq M] [Nonempty M] [∀ e, Fintype (κ e)]
    (b : ∀ e, Basis (κ e) ℂ (W e)) (t : PiTensorProduct ℂ W) :
    MinorsVanish (tensorCoordinates b t) ↔ TensorPureOrZero t := by
  rw [minors_iff_pureOrZero, tensorPureOrZero_coordinates b t]

omit [Fintype M] in
/-- A nonzero pure tensor has nonzero factors, without a supplied hypothesis. -/
theorem nonzero_factors_of_tprod_ne_zero (U : ∀ e, W e)
    (hU : PiTensorProduct.tprod ℂ U ≠ 0) : ∀ e, U e ≠ 0 := by
  intro e he
  exact hU ((PiTensorProduct.tprod ℂ).map_coord_zero e he)

/-- Extend a specified nonzero vector to a basis that literally contains it. -/
theorem exists_basis_containing {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u : E) (hu : u ≠ 0) : ∃ (S : Set E) (b : Basis S ℂ E) (p : S), b p = u := by
  let h : LinearIndepOn ℂ id ({u} : Set E) := (linearIndepOn_singleton_iff ℂ).mpr hu
  let S := h.extend (Set.subset_univ _)
  let p : S := ⟨u, Basis.subset_extend h (Set.mem_singleton u)⟩
  exact ⟨S, Basis.extend h, p, Basis.extend_apply_self h p⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The generic linear-space theorem for a Segre cone. All fixed factors and
the varying factor are conclusions; no ruling is assumed. -/
theorem linear_image_ruling [DecidableEq M] [Nonempty M]
    [∀ e, FiniteDimensional ℂ (W e)]
    (Φ : V →ₗ[ℂ] PiTensorProduct ℂ W) (hΦ : Φ ≠ 0)
    (hpure : ∀ v, TensorPureOrZero (Φ v)) :
    ∃ (e : M) (U : ∀ e, W e) (ψ : V →ₗ[ℂ] W e),
      (∀ f, f ≠ e → U f ≠ 0) ∧
      ∀ v, Φ v = PiTensorProduct.tprod ℂ (update U e (ψ v)) := by
  classical
  have hnonzero : ∃ v₀, Φ v₀ ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hΦ (LinearMap.ext hh)
  obtain ⟨v₀, hv₀⟩ := hnonzero
  obtain hz | ⟨U, hU⟩ := hpure v₀
  · exact (hv₀ hz).elim
  have hUnz : ∀ e, U e ≠ 0 := nonzero_factors_of_tprod_ne_zero U (hU ▸ hv₀)
  choose S b p hbp using fun e => exists_basis_containing (U e) (hUnz e)
  let : ∀ e, Fintype (S e) := fun e => FiniteDimensional.fintypeBasisIndex (b e)
  let C := tensorCoordinates b
  let F : V →ₗ[ℂ] Array (fun e => S e) := C.toLinearMap.comp Φ
  have hF : ∀ v, MinorsVanish (F v) := fun v =>
    (tensor_minors_iff b (Φ v)).mpr (hpure v)
  have hbase : F v₀ = delta p := by
    have ht : Φ v₀ = (Basis.piTensorProduct b) p := by
      rw [Basis.piTensorProduct_apply, hU]
      congr 1
      funext e
      exact (hbp e).symm
    change C (Φ v₀) = _
    rw [ht]
    funext x
    change (Basis.piTensorProduct b).equivFun ((Basis.piTensorProduct b) p) x = delta p x
    rw [Basis.equivFun_self]
    simp only [delta]
    by_cases hxp : x = p
    · subst x; simp
    · simp only [ite_eq_right hxp, ite_eq_right (Ne.symm hxp)]
  obtain ⟨e, he⟩ := coordinate_linear_ruling F hF v₀ p hbase
  let ψ : V →ₗ[ℂ] W e := ((b e).equivFun.symm.toLinearMap).comp (axisSlice F p e)
  refine ⟨e, U, ψ, fun f _ => hUnz f, ?_⟩
  intro v
  apply C.injective
  change F v = _
  rw [he v]
  change _ = tensorCoordinates b _
  rw [tensorCoordinates_tprod]
  congr 1
  funext f
  by_cases hfe : f = e
  · subst f
    simp only [update_self]
    change axisSlice F p e v = (b e).equivFun ((b e).equivFun.symm (axisSlice F p e v))
    exact ((b e).equivFun.apply_symm_apply _).symm
  · rw [update_of_ne hfe, update_of_ne hfe]
    rw [← hbp f]
    funext a
    simp [deltaFactors, Basis.equivFun_self, eq_comm]

end Holant.Platonic.FixedMatchingRuling.Segre
