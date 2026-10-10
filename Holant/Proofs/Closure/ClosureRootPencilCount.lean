import Holant.Polynomial.GridInterpolation
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Finite-support counting for an actual affine root pencil. A nonzero
coordinate vanishes at at most one distinct phase. Double counting its
nonzero incidences bounds the union support without any matching or ruling
hypothesis. The root corollaries use the actual `Laurent.rootCoset m 1`.
These are counting lemmas, not a coefficient-line synthesis theorem. -/
noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencilCount

variable {X K : Type*} [Fintype X] [Field K]

/-- The literal coordinate support of one sampled affine pencil. -/
def pencilSupport (U V : X → K) (t : K) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => U x + t * V x ≠ 0)

/-- Every coordinate occurring in either of the two affine coefficients. -/
def unionSupport (U V : X → K) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => U x ≠ 0 ∨ V x ≠ 0)

@[simp] theorem mem_pencilSupport (U V : X → K) (t : K) (x : X) :
    x ∈ pencilSupport U V t ↔ U x + t * V x ≠ 0 := by
  classical
  simp [pencilSupport]

@[simp] theorem mem_unionSupport (U V : X → K) (x : X) :
    x ∈ unionSupport U V ↔ U x ≠ 0 ∨ V x ≠ 0 := by
  classical
  simp [unionSupport]

theorem pencilSupport_subset_union (U V : X → K) (t : K) :
    pencilSupport U V t ⊆ unionSupport U V := by
  classical
  intro x hx
  apply (mem_unionSupport U V x).mpr
  have hn := (mem_pencilSupport U V t x).mp hx
  by_cases hu : U x = 0
  · right
    intro hv
    exact hn (by simp [hu, hv])
  · exact Or.inl hu

/-- A coordinate with at least one nonzero coefficient has at most one
zero phase in any finite set of distinct field elements. -/
theorem affine_zero_fiber_card_le_one (phases : Finset K) (U V : X → K)
    (x : X) (active : U x ≠ 0 ∨ V x ≠ 0) :
    (phases.filter (fun t => U x + t * V x = 0)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hza := (Finset.mem_filter.mp ha).2
  have hzb := (Finset.mem_filter.mp hb).2
  by_cases hv : V x = 0
  · have hu : U x ≠ 0 := active.resolve_right (fun hn => hn hv)
    exact (hu (by simpa [hv] using hza)).elim
  · exact mul_right_cancel₀ hv (add_left_cancel (hza.trans hzb.symm))

/-- Every active coordinate occurs in all but at most one sample. -/
theorem active_coordinate_degree_lower (phases : Finset K) (U V : X → K)
    (x : X) (active : U x ≠ 0 ∨ V x ≠ 0) :
    phases.card - 1 ≤ (phases.filter (fun t => U x + t * V x ≠ 0)).card := by
  classical
  have hz := affine_zero_fiber_card_le_one phases U V x active
  have hpartition : (phases.filter (fun t => U x + t * V x = 0)).card +
      (phases.filter (fun t => U x + t * V x ≠ 0)).card = phases.card := by
    simpa only [ne_eq] using Finset.card_filter_add_card_filter_not
      (s := phases) (fun t => U x + t * V x = 0)
  omega

/-- Double counting nonzero coordinate/phase incidences on a distinct finite
grid. Neither the union support nor a fixed support pattern is an input. -/
theorem finite_grid_union_count (phases : Finset K) (U V : X → K) (k : ℕ)
    (supportExact : ∀ t ∈ phases, (pencilSupport U V t).card = k) :
    (phases.card - 1) * (unionSupport U V).card ≤ phases.card * k := by
  classical
  let incident : X → K → Prop := fun x t => U x + t * V x ≠ 0
  have lower : ∀ x ∈ unionSupport U V,
      phases.card - 1 ≤ (phases.bipartiteAbove incident x).card := by
    intro x hx
    exact active_coordinate_degree_lower phases U V x ((mem_unionSupport U V x).mp hx)
  have fiber (t : K) : (unionSupport U V).bipartiteBelow incident t =
      pencilSupport U V t := by
    ext x
    constructor
    · intro hx
      exact (mem_pencilSupport U V t x).mpr (Finset.mem_filter.mp hx).2
    · intro hx
      exact Finset.mem_filter.mpr ⟨pencilSupport_subset_union U V t hx,
        (mem_pencilSupport U V t x).mp hx⟩
  have upper : ∀ t ∈ phases,
      ((unionSupport U V).bipartiteBelow incident t).card ≤ k := by
    intro t ht
    simpa only [fiber t] using (supportExact t ht).le
  have counted := Finset.card_mul_le_card_mul
    (s := unionSupport U V) (t := phases)
    (m := phases.card - 1) (n := k) incident lower upper
  calc
    (phases.card - 1) * (unionSupport U V).card =
        (unionSupport U V).card * (phases.card - 1) := Nat.mul_comm _ _
    _ ≤ phases.card * k := counted

/-- Actual m-th roots, with their proved cardinality m. This stronger form
does not need the redundant whole-sample nonzero hypothesis. -/
theorem root_coset_union_count (m : ℕ) [NeZero m] (U V : X → ℂ) (k : ℕ)
    (supportExact : ∀ t ∈ Laurent.rootCoset m 1, (pencilSupport U V t).card = k) :
    (m - 1) * (unionSupport U V).card ≤ m * k := by
  simpa only [Laurent.card_rootCoset] using
    finite_grid_union_count (Laurent.rootCoset m 1) U V k supportExact

/-- The requested actual-root boundary keeps both exact sample hypotheses.
No support-union bound, matching, or desired ruling is assumed. -/
theorem actual_roots_union_count (m : ℕ) [NeZero m] (U V : X → ℂ) (k : ℕ)
    (_sampleNonzero : ∀ t ∈ Laurent.rootCoset m 1, (fun x => U x + t * V x) ≠ 0)
    (supportExact : ∀ t ∈ Laurent.rootCoset m 1, (pencilSupport U V t).card = k) :
    (m - 1) * (unionSupport U V).card ≤ m * k :=
  root_coset_union_count m U V k supportExact

/-- Four-point supports on at least four actual roots have union size at most five. -/
theorem actual_roots_four_union_le_five (m : ℕ) [NeZero m] (hm : 4 ≤ m)
    (U V : X → ℂ)
    (sampleNonzero : ∀ t ∈ Laurent.rootCoset m 1, (fun x => U x + t * V x) ≠ 0)
    (supportExact : ∀ t ∈ Laurent.rootCoset m 1, (pencilSupport U V t).card = 4) :
    (unionSupport U V).card ≤ 5 := by
  have counted := actual_roots_union_count m U V 4 sampleNonzero supportExact
  by_contra h
  have six : 6 ≤ (unionSupport U V).card := by omega
  have lower := Nat.mul_le_mul_left (m - 1) six
  have bound : (m - 1) * 6 ≤ m * 4 := lower.trans counted
  have hsub : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  omega

/-- On the three actual cube roots the same exact assumptions give union size at most six. -/
theorem three_roots_four_union_le_six (U V : X → ℂ)
    (sampleNonzero : ∀ t ∈ Laurent.rootCoset 3 1, (fun x => U x + t * V x) ≠ 0)
    (supportExact : ∀ t ∈ Laurent.rootCoset 3 1, (pencilSupport U V t).card = 4) :
    (unionSupport U V).card ≤ 6 := by
  have counted := actual_roots_union_count 3 U V 4 sampleNonzero supportExact
  omega

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencilCount
