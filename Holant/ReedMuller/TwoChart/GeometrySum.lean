import Holant.ReedMuller.TwoChart.GeometryBasic
import Mathlib.LinearAlgebra.Projection

/-! Orthogonal sums and transport from actual subspaces. -/
namespace Holant.ReedMuller.TwoChart.Geometry
open Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module F₂ V]
variable (B : LinearMap.BilinForm F₂ V)

def SelfOrthogonal (J : Submodule F₂ V) : Prop := ∀ x ∈ J, ∀ y ∈ J, B x y = 0

theorem selfOrthogonal_span_singleton {x : V} (hx : B x x = 0) :
    SelfOrthogonal B (Submodule.span F₂ {x}) := by
  intro u hu v hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
  simp [hx]

theorem selfOrthogonal_map_subtype (P : Submodule F₂ V) (J : Submodule F₂ P)
    (hJ : SelfOrthogonal (B.restrict P) J) : SelfOrthogonal B (J.map P.subtype) := by
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  exact hJ u hu v hv

theorem map_subtype_le (P : Submodule F₂ V) (J : Submodule F₂ P) :
    J.map P.subtype ≤ P := by
  rintro x ⟨u, _, rfl⟩
  exact u.property

theorem nondegenerate_map_subtype (P : Submodule F₂ V) (J : Submodule F₂ P)
    (hJ : ((B.restrict P).restrict J).Nondegenerate) :
    (B.restrict (J.map P.subtype)).Nondegenerate := by
  constructor
  · rintro ⟨x, u, hu, rfl⟩ hx
    have hz : (⟨u, hu⟩ : J) = 0 := hJ.1 ⟨u, hu⟩ (fun v =>
      hx ⟨(v : P), Submodule.mem_map.mpr ⟨v, v.property, rfl⟩⟩)
    apply Subtype.ext
    exact congrArg (fun z : J => ((z : P) : V)) hz
  · rintro ⟨x, u, hu, rfl⟩ hx
    have hz : (⟨u, hu⟩ : J) = 0 := hJ.2 ⟨u, hu⟩ (fun v =>
      hx ⟨(v : P), Submodule.mem_map.mpr ⟨v, v.property, rfl⟩⟩)
    apply Subtype.ext
    exact congrArg (fun z : J => ((z : P) : V)) hz

theorem selfOrthogonal_sup (hB : B.IsSymm) (J K : Submodule F₂ V)
    (hJ : SelfOrthogonal B J) (hK : SelfOrthogonal B K)
    (hJK : K ≤ B.orthogonal J) : SelfOrthogonal B (J ⊔ K) := by
  intro x hx y hy
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u', hu', v', hv', rfl⟩ := Submodule.mem_sup.mp hy
  have huv : B u v' = 0 := hJK hv' u hu
  have hvu : B v u' = 0 := (hB.eq v u').trans (hJK hv u' hu')
  simp [hJ u hu u' hu', hK v hv v' hv', huv, hvu]

theorem nondegenerate_sup (hB : B.IsSymm) (U Q : Submodule F₂ V)
    (hU : (B.restrict U).Nondegenerate) (hQ : (B.restrict Q).Nondegenerate)
    (hQU : Q ≤ B.orthogonal U) : (B.restrict (U ⊔ Q)).Nondegenerate := by
  have hl : ∀ x : ↥(U ⊔ Q), (∀ y : ↥(U ⊔ Q), B x y = 0) → x = 0 := by
    intro x hx
    obtain ⟨u, hu, q, hq, hxq⟩ := Submodule.mem_sup.mp x.property
    have hu0 : (⟨u, hu⟩ : U) = 0 := by
      apply hU.1
      intro y
      have h := hx ⟨y, (show U ≤ U ⊔ Q from le_sup_left) y.property⟩
      change B (x : V) (y : V) = 0 at h
      rw [← hxq] at h
      have hqy : B q y = 0 := (hB.eq q y).trans (hQU hq y y.property)
      simpa [hqy] using h
    have hu' : u = 0 := congrArg Subtype.val hu0
    have hq0 : (⟨q, hq⟩ : Q) = 0 := by
      apply hQ.1
      intro y
      have h := hx ⟨y, (show Q ≤ U ⊔ Q from le_sup_right) y.property⟩
      change B (x : V) (y : V) = 0 at h
      rw [← hxq, hu', zero_add] at h
      exact h
    apply Subtype.ext
    rw [← hxq, hu', show q = 0 from congrArg Subtype.val hq0, add_zero]
    rfl
  exact ⟨hl, fun x hx => hl x (fun y => by rw [hB.eq]; exact hx y)⟩

theorem disjoint_of_le_orthogonal [FiniteDimensional F₂ V]
    (hB : B.IsSymm) (U Q : Submodule F₂ V)
    (hU : (B.restrict U).Nondegenerate) (hQU : Q ≤ B.orthogonal U) : Disjoint U Q :=
  (B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hU).disjoint.mono_right hQU

theorem finrank_sup_of_disjoint [FiniteDimensional F₂ V]
    (U Q : Submodule F₂ V) (hd : Disjoint U Q) :
    finrank F₂ ↥(U ⊔ Q) = finrank F₂ U + finrank F₂ Q := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U Q
  rw [hd.eq_bot, finrank_bot, add_zero] at h
  exact h

theorem selfDual_of_selfOrthogonal_halfDimension [FiniteDimensional F₂ V]
    (hn : B.Nondegenerate) (J : Submodule F₂ V) (hJ : SelfOrthogonal B J)
    (hd : 2 * finrank F₂ J = finrank F₂ V) : J = B.orthogonal J := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx y hy
    exact hJ y hy x hx
  · rw [B.finrank_orthogonal hn]
    omega

end
end Holant.ReedMuller.TwoChart.Geometry
