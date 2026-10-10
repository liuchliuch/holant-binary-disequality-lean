import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Projectivization.Collinear
import Mathlib.LinearAlgebra.Quotient.Defs

/-! The intrinsic quotient direction in Proposition A.19, over an arbitrary complex
vector space. The quotient is by the actual one-dimensional submodule of the base
point, and equality is characterized by genuine projective collinearity. -/

namespace Holant.Certificates.PlatonicAtlas

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A nonzero vector lies on a projective point exactly when it represents it. -/
theorem mk_eq_iff_mem_point_submodule (p : Projectivization ℂ V)
    (v : V) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv = p ↔ v ∈ p.submodule := by
  rw [p.submodule_eq, Submodule.mem_span_singleton]
  simpa only [Projectivization.mk_rep] using
    (Projectivization.mk_eq_mk_iff' ℂ v p.rep hv p.rep_nonzero)

/-- The quotient of a representative of a different point is nonzero. -/
theorem quotient_rep_ne_zero (p q : Projectivization ℂ V) (hq : q ≠ p) :
    p.submodule.mkQ q.rep ≠ 0 := by
  intro h
  apply hq
  rw [← q.mk_rep, mk_eq_iff_mem_point_submodule]
  exact (Submodule.Quotient.mk_eq_zero p.submodule).mp h

/-- The direction of `q` from `p`, as a projective point in the actual vector-space
quotient by the line of `p`. -/
def quotientDirection (p q : Projectivization ℂ V) (hq : q ≠ p) :
    Projectivization ℂ (V ⧸ p.submodule) :=
  Projectivization.mk ℂ (p.submodule.mkQ q.rep) (quotient_rep_ne_zero p q hq)

/-- Any nonzero representative of a point different from the base survives in the quotient. -/
theorem quotient_representative_ne_zero (p q : Projectivization ℂ V) (hq : q ≠ p)
    (v : V) (hv : v ≠ 0) (hvq : Projectivization.mk ℂ v hv = q) :
    p.submodule.mkQ v ≠ 0 := by
  intro h
  apply hq
  rw [← hvq, mk_eq_iff_mem_point_submodule]
  exact (Submodule.Quotient.mk_eq_zero p.submodule).mp h

/-- Formula for the intrinsic direction using any nonzero representative of `q`. -/
theorem quotientDirection_eq_mk (p q : Projectivization ℂ V) (hq : q ≠ p)
    (v : V) (hv : v ≠ 0) (hvq : Projectivization.mk ℂ v hv = q) :
    quotientDirection p q hq = Projectivization.mk ℂ (p.submodule.mkQ v)
      (quotient_representative_ne_zero p q hq v hv hvq) := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ q.rep v q.rep_nonzero hv).mp
    (q.mk_rep.trans hvq.symm)
  exact ⟨a, by simpa only [map_smul] using congrArg p.submodule.mkQ ha⟩

/-- Changing the nonzero representative of the base leaves its quotient submodule unchanged. -/
theorem span_representative_eq_point_submodule (p : Projectivization ℂ V)
    (v : V) (hv : v ≠ 0) (hvp : Projectivization.mk ℂ v hv = p) :
    Submodule.span ℂ ({v} : Set V) = p.submodule := by
  rw [← hvp, Projectivization.submodule_mk]

/-- The quotient vector in the source's formula is nonzero for arbitrary choices
of nonzero representatives of both points. -/
theorem quotient_representatives_ne_zero (p q : Projectivization ℂ V) (hq : q ≠ p)
    (u : V) (hu : u ≠ 0) (hup : Projectivization.mk ℂ u hu = p)
    (v : V) (hv : v ≠ 0) (hvq : Projectivization.mk ℂ v hv = q) :
    (Submodule.span ℂ ({u} : Set V)).mkQ v ≠ 0 := by
  rw [span_representative_eq_point_submodule p u hu hup]
  exact quotient_representative_ne_zero p q hq v hv hvq

/-- The formula with arbitrary nonzero representatives of both points agrees
with the intrinsic direction after the canonical identification of quotients. -/
theorem quotientDirection_eq_mk_representatives (p q : Projectivization ℂ V) (hq : q ≠ p)
    (u : V) (hu : u ≠ 0) (hup : Projectivization.mk ℂ u hu = p)
    (v : V) (hv : v ≠ 0) (hvq : Projectivization.mk ℂ v hv = q) :
    let e := Submodule.quotEquivOfEq (Submodule.span ℂ ({u} : Set V)) p.submodule
      (span_representative_eq_point_submodule p u hu hup)
    Projectivization.map e.toLinearMap e.injective
      (Projectivization.mk ℂ ((Submodule.span ℂ ({u} : Set V)).mkQ v)
        (quotient_representatives_ne_zero p q hq u hu hup v hv hvq)) =
      quotientDirection p q hq := by
  dsimp only
  rw [Projectivization.map_mk]
  exact (quotientDirection_eq_mk p q hq v hv hvq).symm

/-- Equality of quotient directions is precisely proportionality modulo the base line. -/
theorem quotientDirection_eq_iff_scalar_mod_submodule (p q r : Projectivization ℂ V)
    (hq : q ≠ p) (hr : r ≠ p) :
    quotientDirection p q hq = quotientDirection p r hr ↔
      ∃ c : ℂ, r.rep - c • q.rep ∈ p.submodule := by
  change Projectivization.mk ℂ (p.submodule.mkQ q.rep) _ =
    Projectivization.mk ℂ (p.submodule.mkQ r.rep) _ ↔ _
  rw [eq_comm, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, Submodule.Quotient.eq p.submodule |>.mp ?_⟩
    simpa only [← Submodule.mkQ_apply, map_smul] using hc.symm
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have he := (Submodule.Quotient.eq p.submodule).mpr hc
    simpa only [← Submodule.mkQ_apply, map_smul] using he.symm

/-- The scalar in the quotient proportionality criterion is necessarily nonzero. -/
theorem quotientDirection_eq_iff_nonzero_scalar_mod_span (p q r : Projectivization ℂ V)
    (hq : q ≠ p) (hr : r ≠ p) :
    quotientDirection p q hq = quotientDirection p r hr ↔
      ∃ c : ℂ, c ≠ 0 ∧ r.rep - c • q.rep ∈ Submodule.span ℂ ({p.rep} : Set V) := by
  rw [quotientDirection_eq_iff_scalar_mod_submodule, p.submodule_eq]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc⟩
    intro hz
    apply hr
    rw [← r.mk_rep, mk_eq_iff_mem_point_submodule, p.submodule_eq]
    simpa [hz] using hc
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

/-- Quotient-direction fibers are actual two-vector spans. -/
theorem quotientDirection_eq_iff_mem_span (p q r : Projectivization ℂ V)
    (hq : q ≠ p) (hr : r ≠ p) :
    quotientDirection p q hq = quotientDirection p r hr ↔
      r.rep ∈ Submodule.span ℂ ({p.rep, q.rep} : Set V) := by
  rw [quotientDirection_eq_iff_scalar_mod_submodule, p.submodule_eq,
    Submodule.mem_span_pair]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hc
    exact ⟨a, c, by rw [ha, sub_add_cancel]⟩
  · rintro ⟨a, c, h⟩
    refine ⟨c, Submodule.mem_span_singleton.mpr ⟨a, ?_⟩⟩
    rw [← h, add_sub_cancel_right]

/-- The span criterion holds for any nonzero representatives of all three points. -/
theorem quotientDirection_eq_iff_representative_mem_span (p q r : Projectivization ℂ V)
    (hq : q ≠ p) (hr : r ≠ p)
    (u : V) (hu : u ≠ 0) (hup : Projectivization.mk ℂ u hu = p)
    (v : V) (hv : v ≠ 0) (hvq : Projectivization.mk ℂ v hv = q)
    (w : V) (hw : w ≠ 0) (hwr : Projectivization.mk ℂ w hw = r) :
    quotientDirection p q hq = quotientDirection p r hr ↔
      w ∈ Submodule.span ℂ ({u, v} : Set V) := by
  have hs : Submodule.span ℂ ({u, v} : Set V) =
      Submodule.span ℂ ({p.rep, q.rep} : Set V) := by
    rw [Submodule.span_insert, Submodule.span_insert,
      span_representative_eq_point_submodule p u hu hup,
      span_representative_eq_point_submodule q v hv hvq,
      p.submodule_eq, q.submodule_eq]
  rw [quotientDirection_eq_iff_mem_span, hs]
  let L := Submodule.span ℂ ({p.rep, q.rep} : Set V)
  change r.rep ∈ L ↔ w ∈ L
  rw [← Submodule.mk_mem_projectivization_iff L r.rep_nonzero,
    ← Submodule.mk_mem_projectivization_iff L hw, r.mk_rep, hwr]

/-- The actual vector span of two distinct projective points has dimension two. -/
theorem point_pair_span_finrank (p q : Projectivization ℂ V) (hq : q ≠ p) :
    Module.finrank ℂ (Submodule.span ℂ ({p.rep, q.rep} : Set V)) = 2 := by
  have hi : LinearIndependent ℂ ![p.rep, q.rep] :=
    Projectivization.linearIndependent_pair_iff_ne.mpr hq.symm
  rw [← Matrix.range_cons_cons_empty p.rep q.rep ![]]
  simpa using finrank_span_eq_card hi

/-- Native projective collinearity is equivalent to membership in the genuine secant span. -/
theorem isCollinear_triple_iff_mem_span (p q r : Projectivization ℂ V) (hq : q ≠ p) :
    Projectivization.IsCollinear ({p, q, r} : Set (Projectivization ℂ V)) ↔
      r.rep ∈ Submodule.span ℂ ({p.rep, q.rep} : Set V) := by
  let L := Submodule.span ℂ ({p.rep, q.rep} : Set V)
  have hpL : p ∈ L.projectivization := by
    rw [← p.mk_rep, Submodule.mk_mem_projectivization_iff]
    exact Submodule.subset_span (by simp)
  have hqL : q ∈ L.projectivization := by
    rw [← q.mk_rep, Submodule.mk_mem_projectivization_iff]
    exact Submodule.subset_span (by simp)
  constructor
  · rintro ⟨M, hMfinite, hMdim, hM⟩
    have := hMfinite
    have hpM : p.rep ∈ M.submodule :=
      (Projectivization.Subspace.mem_submodule_iff M p.rep_nonzero).mpr
        (by simpa using hM (by simp : p ∈ ({p, q, r} : Set _)))
    have hqM : q.rep ∈ M.submodule :=
      (Projectivization.Subspace.mem_submodule_iff M q.rep_nonzero).mpr
        (by simpa using hM (by simp : q ∈ ({p, q, r} : Set _)))
    have hrM : r.rep ∈ M.submodule :=
      (Projectivization.Subspace.mem_submodule_iff M r.rep_nonzero).mpr
        (by simpa using hM (by simp : r ∈ ({p, q, r} : Set _)))
    have hLM : L ≤ M.submodule := Submodule.span_le.mpr (by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hpM
      · simpa only [Set.mem_singleton_iff] using hx ▸ hqM)
    have he : L = M.submodule := Submodule.eq_of_le_of_finrank_le hLM (by
      simpa only [L, point_pair_span_finrank p q hq] using hMdim)
    change r.rep ∈ L
    rw [he]
    exact hrM
  · intro hrL
    refine ⟨L.projectivization, ?_, ?_, ?_⟩
    · rw [Projectivization.Subspace.submodule.apply_symm_apply]
      exact Module.Finite.span_of_finite _ (Set.toFinite _)
    · rw [Projectivization.Subspace.submodule.apply_symm_apply]
      exact (point_pair_span_finrank p q hq).le
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · exact hx ▸ hpL
      · exact hx ▸ hqL
      · subst x
        change r ∈ L.projectivization
        rw [← r.mk_rep, Submodule.mk_mem_projectivization_iff]
        exact hrL

/-- Two points have the same quotient direction exactly when they and the base
lie on one projective line, using Mathlib's intrinsic collinearity predicate. -/
theorem quotientDirection_eq_iff_isCollinear (p q r : Projectivization ℂ V)
    (hq : q ≠ p) (hr : r ≠ p) :
    quotientDirection p q hq = quotientDirection p r hr ↔
      Projectivization.IsCollinear ({p, q, r} : Set (Projectivization ℂ V)) :=
  (quotientDirection_eq_iff_mem_span p q r hq hr).trans
    (isCollinear_triple_iff_mem_span p q r hq).symm

open scoped Classical

/-- A quotient-direction bucket of a finite projective configuration. The base
is omitted because it has zero image in the quotient. -/
def quotientDirectionFiber (D : Finset (Projectivization ℂ V))
    (p q : Projectivization ℂ V) (hq : q ≠ p) : Finset (Projectivization ℂ V) :=
  D.filter (fun r => ∃ hr : r ≠ p, quotientDirection p r hr = quotientDirection p q hq)

/-- A bucket consists exactly of the non-base points on its actual secant. -/
theorem mem_quotientDirectionFiber (D : Finset (Projectivization ℂ V))
    (p q r : Projectivization ℂ V) (hq : q ≠ p) :
    r ∈ quotientDirectionFiber D p q hq ↔
      r ∈ D ∧ r ≠ p ∧ r.rep ∈ Submodule.span ℂ ({p.rep, q.rep} : Set V) := by
  simp only [quotientDirectionFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hrD, hr, h⟩
    exact ⟨hrD, hr, (quotientDirection_eq_iff_mem_span p q r hq hr).mp h.symm⟩
  · rintro ⟨hrD, hr, h⟩
    exact ⟨hrD, hr, ((quotientDirection_eq_iff_mem_span p q r hq hr).mpr h).symm⟩

/-- Quotient buckets are full actual secant intersections with the base erased. -/
theorem quotientDirectionFiber_eq_secant_filter (D : Finset (Projectivization ℂ V))
    (p q : Projectivization ℂ V) (hq : q ≠ p) :
    quotientDirectionFiber D p q hq =
      (D.erase p).filter (fun r => r.rep ∈ Submodule.span ℂ ({p.rep, q.rep} : Set V)) := by
  ext r
  simp only [mem_quotientDirectionFiber, Finset.mem_filter, Finset.mem_erase]
  tauto

end
end Holant.Certificates.PlatonicAtlas
