import Holant.ReedMuller.TwoChart.GeometryEnvelope
import Holant.ReedMuller.TwoChart.GeometryLagrangian
import Holant.ReedMuller.TwoChart.GeometryIsometry
import Holant.ReedMuller.RadonAccess.Plane

/-! Apply the abstract binary-space geometry to the literal Radon plane and
its ambient-coordinate orthogonal complement. -/
namespace Holant.ReedMuller.TwoChart.Geometry
open Module
open Holant.ReedMuller.LowArity Holant.ReedMuller.RadonAccess Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem dotBilinear_symmetric : (dotBilinear (n := n)).IsSymm := ⟨dot_comm⟩

namespace RadonGeometry

theorem complement_eq_orthogonal (F : RadonFrame n) :
    F.complement = (dotBilinear (n := n)).orthogonal F.plane := by
  ext x
  exact F.complement_iff_orthogonal_plane x

theorem plane_finrank (F : RadonFrame n) : finrank F₂ F.plane = 2 := by
  simpa using F.planeLinearEquiv.finrank_eq

theorem complement_finrank (F : RadonFrame n) : finrank F₂ F.complement = n - 2 := by
  rw [complement_eq_orthogonal F,
    LinearMap.BilinForm.finrank_orthogonal dotBilinear_nondegenerate, plane_finrank]
  simp [BinaryVector]

theorem two_add_complement_finrank (F : RadonFrame n) :
    2 + finrank F₂ F.complement = n := by
  have h := finrank_add_orthogonal (dotBilinear (n := n)) dotBilinear_nondegenerate F.plane
  rw [plane_finrank, ← complement_eq_orthogonal F] at h
  simpa [BinaryVector] using h

theorem complement_even (F : RadonFrame n) (hn : Even n) :
    Even (finrank F₂ F.complement) := by
  have h := two_add_complement_finrank F
  obtain ⟨k, hk⟩ := hn
  exact ⟨k - 1, by omega⟩

theorem complement_nondegenerate (F : RadonFrame n) :
    ((dotBilinear (n := n)).restrict F.complement).Nondegenerate := by
  have hl : ∀ x : F.complement, (∀ y : F.complement, dot (x : BinaryVector n) y = 0) → x = 0 :=
    fun x hx => Subtype.ext (F.complement_nondegenerate x hx)
  exact ⟨hl, fun x hx => hl x (fun y => by rw [dot_comm]; exact hx y)⟩

theorem plane_nondegenerate (F : RadonFrame n) :
    ((dotBilinear (n := n)).restrict F.plane).Nondegenerate := by
  have hl : ∀ x : F.plane, (∀ y : F.plane, dot (x : BinaryVector n) y = 0) → x = 0 :=
    fun x hx => Subtype.ext (F.plane_nondegenerate x hx)
  exact ⟨hl, fun x hx => hl x (fun y => by rw [dot_comm]; exact hx y)⟩

/-- Retain the physical Radon plane together with a chosen quotient subspace. -/
def retainedSpace (F : RadonFrame n) (U : Submodule F₂ F.complement) : BinaryCode n :=
  F.plane ⊔ U.map F.complement.subtype

theorem r_mem_retainedSpace (F : RadonFrame n) (U : Submodule F₂ F.complement) :
    F.r ∈ retainedSpace F U :=
  Submodule.mem_sup_left (Submodule.subset_span (by simp))

theorem v_mem_retainedSpace (F : RadonFrame n) (U : Submodule F₂ F.complement) :
    F.v ∈ retainedSpace F U :=
  Submodule.mem_sup_left (Submodule.subset_span (by simp))

theorem mem_retainedSpace_of_mem (F : RadonFrame n) (U : Submodule F₂ F.complement)
    (u : F.complement) (hu : u ∈ U) : (u : BinaryVector n) ∈ retainedSpace F U :=
  Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨u, hu, rfl⟩)

theorem retainedSpace_nondegenerate (F : RadonFrame n) (U : Submodule F₂ F.complement)
    (hU : (((dotBilinear (n := n)).restrict F.complement).restrict U).Nondegenerate) :
    ((dotBilinear (n := n)).restrict (retainedSpace F U)).Nondegenerate := by
  apply nondegenerate_sup _ dotBilinear_symmetric _ _ (plane_nondegenerate F)
    (nondegenerate_map_subtype _ F.complement U hU)
  rw [← complement_eq_orthogonal F]
  exact map_subtype_le F.complement U

theorem retainedSpace_finrank (F : RadonFrame n) (U : Submodule F₂ F.complement) :
    finrank F₂ (retainedSpace F U) = 2 + finrank F₂ U := by
  have hdis : Disjoint F.plane (U.map F.complement.subtype) := by
    apply disjoint_of_le_orthogonal _ dotBilinear_symmetric _ _ (plane_nondegenerate F)
    rw [← complement_eq_orthogonal F]
    exact map_subtype_le F.complement U
  rw [retainedSpace, finrank_sup_of_disjoint _ _ hdis, plane_finrank,
    Submodule.finrank_map_subtype_eq]

theorem retainedSpace_even (F : RadonFrame n) (U : Submodule F₂ F.complement)
    (hU : Even (finrank F₂ U)) : Even (finrank F₂ (retainedSpace F U)) := by
  rw [retainedSpace_finrank]
  exact (by decide : Even 2).add hU

theorem retainedSpace_finrank_le_eight (F : RadonFrame n)
    (U : Submodule F₂ F.complement) (hU : finrank F₂ U ≤ 6) :
    finrank F₂ (retainedSpace F U) ≤ 8 := by
  rw [retainedSpace_finrank]
  omega

/-- Even if `U` is alternating, the retained physical plane provides the
anisotropic vector needed for standard-dot output coordinates. -/
theorem retainedSpace_standard_dot_isometry (F : RadonFrame n)
    (U : Submodule F₂ F.complement)
    (hU : (((dotBilinear (n := n)).restrict F.complement).restrict U).Nondegenerate) :
    ∃ e : retainedSpace F U ≃ₗ[F₂] BinaryVector (finrank F₂ (retainedSpace F U)),
      ∀ x y, dot (e x) (e y) = dot (x : BinaryVector n) y := by
  apply exists_standard_dot_isometry _ (dotBilinear_symmetric.restrict _)
    (retainedSpace_nondegenerate F U hU)
  refine ⟨⟨F.r, r_mem_retainedSpace F U⟩, ?_⟩
  exact F.dot_rr

/-- Original-coordinate localizer data. The isotropic subspace is constructed
inside the relative orthogonal complement and then mapped back into the input
coordinates. These are precisely the hypotheses of the self-dual relation
construction. -/
theorem exists_localizing_data (F : RadonFrame n) (hn : Even n)
    (U : Submodule F₂ F.complement)
    (hU : (((dotBilinear (n := n)).restrict F.complement).restrict U).Nondegenerate)
    (heU : Even (finrank F₂ U)) :
    ∃ (J : BinaryCode n)
      (phi : retainedSpace F U ≃ₗ[F₂] BinaryVector (finrank F₂ (retainedSpace F U))),
      (∀ s t, dot (phi s) (phi t) = dot (s : BinaryVector n) t) ∧
      (∀ j ∈ J, ∀ k ∈ J, dot j k = 0) ∧
      (∀ s ∈ retainedSpace F U, ∀ j ∈ J, dot s j = 0) ∧
      finrank F₂ (retainedSpace F U) + 2 * finrank F₂ J = n ∧
      J ≤ (dotBilinear (n := n)).orthogonal (retainedSpace F U) := by
  let S := retainedSpace F U
  let B := dotBilinear (n := n)
  let P := B.orthogonal S
  have hnS := retainedSpace_nondegenerate F U hU
  have heS := retainedSpace_even F U heU
  have hdim : finrank F₂ S + finrank F₂ P = n := by
    simpa [BinaryVector] using finrank_add_orthogonal B dotBilinear_nondegenerate S
  have heP : Even (finrank F₂ P) := by
    obtain ⟨k, hk⟩ := hn
    obtain ⟨l, hl⟩ := heS
    exact ⟨k - l, by dsimp [S] at hdim; omega⟩
  have hnP := orthogonal_nondegenerate B dotBilinear_symmetric dotBilinear_nondegenerate S hnS
  obtain ⟨K, hK, hdK⟩ := exists_halfDimension_selfOrthogonal
    (B.restrict P) (dotBilinear_symmetric.restrict P) hnP heP
  let J := K.map P.subtype
  have hJP : J ≤ P := map_subtype_le P K
  have hdJ : finrank F₂ J = finrank F₂ K := Submodule.finrank_map_subtype_eq P K
  obtain ⟨phi, hphi⟩ := retainedSpace_standard_dot_isometry F U hU
  refine ⟨J, phi, hphi, selfOrthogonal_map_subtype B P K hK, ?_, ?_, hJP⟩
  · intro s hs j hj
    exact hJP hj s hs
  · rw [hdJ]
    change finrank F₂ S + 2 * finrank F₂ K = n
    omega

end RadonGeometry
end
end Holant.ReedMuller.TwoChart.Geometry
