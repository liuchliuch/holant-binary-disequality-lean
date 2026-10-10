import Holant.ReedMuller.LowArity.HalfDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Elementary orthogonal splitting for symmetric bilinear spaces over `𝔽₂`.
The two-planes used here may be alternating. -/
namespace Holant.ReedMuller.TwoChart.Geometry

open Module LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev F₂ := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module F₂ V]

theorem scalar_eq_zero_or_one (a : F₂) : a = 0 ∨ a = 1 := by
  have h : ∀ a : F₂, a = 0 ∨ a = 1 := by decide
  exact h a

theorem scalar_eq_one_of_ne_zero {a : F₂} (ha : a ≠ 0) : a = 1 :=
  (scalar_eq_zero_or_one a).resolve_left ha

@[simp] theorem vector_add_self (x : V) : x + x = 0 := by
  rw [← two_smul F₂ x]
  rw [show (2 : F₂) = 0 by decide, zero_smul]

def diagonal (B : LinearMap.BilinForm F₂ V) (hB : B.IsSymm) : V →ₗ[F₂] F₂ where
  toFun x := B x x
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply]
    rw [hB.eq y x]
    have h := vector_add_self (B x y)
    linear_combination h
  map_smul' c x := by
    rcases scalar_eq_zero_or_one c with rfl | rfl <;> simp

theorem exists_isotropic_of_two_le [FiniteDimensional F₂ V]
    (B : LinearMap.BilinForm F₂ V) (hB : B.IsSymm) (hd : 2 ≤ finrank F₂ V) :
    ∃ x : V, x ≠ 0 ∧ B x x = 0 := by
  let d := diagonal B hB
  have hr := d.finrank_range_add_finrank_ker
  have hb : finrank F₂ d.range ≤ 1 := by
    simpa using d.range.finrank_le
  have hk : d.ker ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨x, hx, hn⟩ := d.ker.ne_bot_iff.mp hk
  exact ⟨x, hn, hx⟩

theorem exists_pairing_one (B : LinearMap.BilinForm F₂ V) (hB : B.Nondegenerate)
    {x : V} (hx : x ≠ 0) : ∃ y : V, B x y = 1 := by
  by_contra! h
  apply hx
  apply hB.1 x
  intro y
  exact (scalar_eq_zero_or_one (B x y)).resolve_right (h y)

/-- A nondegenerate plane displayed by an isotropic vector and a partner. -/
structure IsotropicPair (B : LinearMap.BilinForm F₂ V) where
  x : V
  y : V
  xx : B x x = 0
  xy : B x y = 1
  yx : B y x = 1

namespace IsotropicPair
variable {B : LinearMap.BilinForm F₂ V} (p : IsotropicPair B)

def space : Submodule F₂ V := Submodule.span F₂ {p.x, p.y}

theorem x_mem : p.x ∈ p.space := Submodule.subset_span (by simp)
theorem y_mem : p.y ∈ p.space := Submodule.subset_span (by simp)

theorem mem_space (z : V) : z ∈ p.space ↔ ∃ a b : F₂, a • p.x + b • p.y = z :=
  Submodule.mem_span_pair

theorem x_ne_zero : p.x ≠ 0 := by
  intro h
  have hh := p.xy
  simp [h] at hh

theorem coefficients_zero {a b : F₂} (h : a • p.x + b • p.y = 0) :
    a = 0 ∧ b = 0 := by
  have hb := congrArg (fun z => B z p.x) h
  have ha := congrArg (fun z => B z p.y) h
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, p.xx, p.yx, mul_zero, mul_one, zero_add, map_zero,
    LinearMap.zero_apply] at hb
  simp [hb, p.xy] at ha
  exact ⟨ha, hb⟩

theorem finrank_space : finrank F₂ p.space = 2 := by
  have hi : LinearIndependent F₂ ![p.x, p.y] :=
    LinearIndependent.pair_iff.mpr (fun a b h => p.coefficients_zero h)
  have hr : Set.range ![p.x, p.y] = ({p.x, p.y} : Set V) := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  change finrank F₂ (Submodule.span F₂ {p.x, p.y}) = 2
  rw [← hr]
  simpa using finrank_span_eq_card hi

theorem nondegenerate (hB : B.IsSymm) : (B.restrict p.space).Nondegenerate := by
  have hl : ∀ z : p.space, (∀ w : p.space, B z w = 0) → z = 0 := by
    intro z hz
    obtain ⟨a, b, hab⟩ := (p.mem_space z).mp z.property
    have hx := hz ⟨p.x, p.x_mem⟩
    have hy := hz ⟨p.y, p.y_mem⟩
    change B (z : V) p.x = 0 at hx
    change B (z : V) p.y = 0 at hy
    rw [← hab] at hx hy
    have hb : b = 0 := by simpa [p.xx, p.yx] using hx
    have ha : a = 0 := by simpa [hb, p.xy] using hy
    apply Subtype.ext
    simp [← hab, ha, hb]
  exact ⟨hl, fun z hz => hl z (fun w => by rw [hB.eq]; exact hz w)⟩

end IsotropicPair

theorem exists_isotropicPair [FiniteDimensional F₂ V]
    (B : LinearMap.BilinForm F₂ V) (hB : B.IsSymm) (hn : B.Nondegenerate)
    (hd : 2 ≤ finrank F₂ V) : Nonempty (IsotropicPair B) := by
  obtain ⟨x, hx, hxx⟩ := exists_isotropic_of_two_le B hB hd
  obtain ⟨y, hxy⟩ := exists_pairing_one B hn hx
  exact ⟨⟨x, y, hxx, hxy, (hB.eq y x).trans hxy⟩⟩

theorem orthogonal_nondegenerate [FiniteDimensional F₂ V]
    (B : LinearMap.BilinForm F₂ V) (hB : B.IsSymm) (hn : B.Nondegenerate)
    (U : Submodule F₂ V) (hU : (B.restrict U).Nondegenerate) :
    (B.restrict (B.orthogonal U)).Nondegenerate := by
  apply B.nondegenerate_restrict_of_disjoint_orthogonal hB.isRefl
  rw [B.orthogonal_orthogonal hn hB.isRefl]
  exact (B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hU).disjoint.symm

theorem finrank_add_orthogonal [FiniteDimensional F₂ V]
    (B : LinearMap.BilinForm F₂ V) (hn : B.Nondegenerate) (U : Submodule F₂ V) :
    finrank F₂ U + finrank F₂ (B.orthogonal U) = finrank F₂ V := by
  rw [B.finrank_orthogonal hn]
  exact Nat.add_sub_of_le U.finrank_le

end
end Holant.ReedMuller.TwoChart.Geometry
