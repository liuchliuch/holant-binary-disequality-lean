import Holant.ReedMuller.LowArity.HalfDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Finite-dimensional geometry in the affine-to-flat Radon argument.
The orthogonal complements here are taken for the literal binary dot form.
The statements are conditional geometry lemmas, not Radon recognition. -/
namespace Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Standard-coordinate orthogonal complement. -/
def dotOrthogonal (U : BinaryCode n) : BinaryCode n := dotBilinear.orthogonal U

@[simp] theorem mem_dotOrthogonal (U : BinaryCode n) (x : BinaryVector n) :
    x ∈ dotOrthogonal U ↔ ∀ y, y ∈ U → dot y x = 0 := Iff.rfl

theorem selfDual_iff_eq_dotOrthogonal (U : BinaryCode n) :
    SelfDual U ↔ U = dotOrthogonal U := by
  constructor
  · intro h
    ext x
    simpa only [mem_dotOrthogonal, dot_comm] using h x
  · intro h x
    rw [h]
    constructor
    · intro hx y hy
      rw [← h] at hy
      rw [dot_comm]
      exact hx y hy
    · intro hx y hy
      change dot y x = 0
      rw [dot_comm]
      exact hx y (h ▸ hy)

/-- The even-word hyperplane `onesᗮ`. -/
def evenSpace (n : ℕ) : BinaryCode n := (dotBilinear (ones n)).ker

@[simp] theorem mem_evenSpace (x : BinaryVector n) :
    x ∈ evenSpace n ↔ dot (ones n) x = 0 := Iff.rfl

theorem finrank_dotOrthogonal (U : BinaryCode n) :
    Module.finrank (ZMod 2) (dotOrthogonal U) = n - Module.finrank (ZMod 2) U := by
  simpa [dotOrthogonal, BinaryVector] using
    LinearMap.BilinForm.finrank_orthogonal (B := dotBilinear) dotBilinear_nondegenerate U

theorem ones_ne_zero (hn : 0 < n) : ones n ≠ 0 := by
  intro h
  have hh := congrFun h (⟨0, hn⟩ : Fin n)
  simp [ones] at hh

theorem evenSpace_eq_orthogonal_span :
    evenSpace n = dotOrthogonal (Submodule.span (ZMod 2) {ones n}) := by
  ext x
  constructor
  · intro hx
    change ∀ y, y ∈ Submodule.span (ZMod 2) {ones n} → dot y x = 0
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [dot_smul_left, (mem_evenSpace x).mp hx, mul_zero]
  · intro hx
    exact hx (ones n) (Submodule.subset_span (Set.mem_singleton _))

theorem finrank_evenSpace (hn : 0 < n) :
    Module.finrank (ZMod 2) (evenSpace n) = n - 1 := by
  rw [evenSpace_eq_orthogonal_span, finrank_dotOrthogonal,
    finrank_span_singleton (ones_ne_zero hn)]

theorem finrank_le_one_of_evenSpace_le_dotOrthogonal (hn : 0 < n)
    (U : BinaryCode n) (h : evenSpace n ≤ dotOrthogonal U) :
    Module.finrank (ZMod 2) U ≤ 1 := by
  have hh := Submodule.finrank_mono h
  rw [finrank_evenSpace hn, finrank_dotOrthogonal] at hh
  have hu : Module.finrank (ZMod 2) U ≤ n := by
    simpa [BinaryVector] using Submodule.finrank_le U
  omega

/-- Intersecting the even hyperplane loses at most one dimension. -/
theorem finrank_evenSpace_inf_lower (hn : 0 < n) (W : BinaryCode n) :
    Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) ↥(evenSpace n ⊓ W) + 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (evenSpace n) W
  have hle := Submodule.finrank_le (evenSpace n ⊔ W)
  rw [finrank_evenSpace hn] at h
  have hv : Module.finrank (ZMod 2) (BinaryVector n) = n := by simp [BinaryVector]
  rw [hv] at hle
  omega

theorem finrank_evenSpace_inf_of_not_le (hn : 0 < n) (W : BinaryCode n)
    (hW : ¬ W ≤ evenSpace n) :
    Module.finrank (ZMod 2) ↥(evenSpace n ⊓ W) + 1 = Module.finrank (ZMod 2) W := by
  have hl := finrank_evenSpace_inf_lower hn W
  have hs : evenSpace n ⊓ W < W := lt_of_le_of_ne inf_le_right (by
    intro h
    exact hW (h ▸ inf_le_left))
  have hu := Submodule.finrank_lt_finrank_of_lt hs
  omega

/-- Accessible membership recovers the excluded all-one vector as a sum of
two accessible vectors; zero is handled by submodule closure. -/
theorem even_subspace_le_of_accessible_le (W U : BinaryCode n)
    (heven : W ≤ evenSpace n) (hdim : 2 ≤ Module.finrank (ZMod 2) W)
    (hacc : ∀ x, x ∈ W → Accessible x → x ∈ U) : W ≤ U := by
  have hline : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {ones n}) ≤ 1 := by
    simpa using finrank_span_le_card (R := ZMod 2) ({ones n} : Set (BinaryVector n))
  have hnot : ¬ W ≤ Submodule.span (ZMod 2) {ones n} := by
    intro h
    have hh := (Submodule.finrank_mono h).trans hline
    omega
  change ¬ ∀ z, z ∈ W → z ∈ Submodule.span (ZMod 2) {ones n} at hnot
  push Not at hnot
  obtain ⟨z, hz, hzn⟩ := hnot
  have hz0 : z ≠ 0 := by intro h; subst z; exact hzn (Submodule.zero_mem _)
  have hz1 : z ≠ ones n := by
    intro h; subst z; exact hzn (Submodule.subset_span (Set.mem_singleton _))
  have hzU : z ∈ U := hacc z hz ⟨heven hz, hz0, hz1⟩
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hx1 : x = ones n
  · subst x
    have hdiff : z - ones n ∈ W := W.sub_mem hz hx
    have hdiff0 : z - ones n ≠ 0 := by intro h; exact hz1 (sub_eq_zero.mp h)
    have hdiff1 : z - ones n ≠ ones n := by
      intro h
      have hh : z = ones n + ones n := sub_eq_iff_eq_add.mp h
      have hadd : ones n + ones n = 0 := by ext i; exact add_self_zero _
      exact hz0 (hh.trans hadd)
    have hdU := hacc (z - ones n) hdiff ⟨heven hdiff, hdiff0, hdiff1⟩
    simpa only [sub_sub_cancel] using U.sub_mem hzU hdU
  · exact hacc x hx ⟨heven hx, hx0, hx1⟩

theorem even_inter_orthogonal_le {r : ℕ} (hr : 4 ≤ r) (U : BinaryCode (2*r))
    (hdim : Module.finrank (ZMod 2) U = r)
    (hacc : ∀ v, Accessible v → v ∈ dotOrthogonal U → v ∈ U) :
    evenSpace (2*r) ⊓ dotOrthogonal U ≤ U := by
  have ho : Module.finrank (ZMod 2) (dotOrthogonal U) = r := by
    rw [finrank_dotOrthogonal, hdim]; omega
  have hl := finrank_evenSpace_inf_lower (by omega : 0 < 2*r) (dotOrthogonal U)
  rw [ho] at hl
  exact even_subspace_le_of_accessible_le _ U inf_le_left (by omega)
    (fun v hv ha => hacc v ha hv.2)

/-- The genuine half-dimensional geometric dichotomy used in source 7.19.
In the second branch the supremum and disjointness give the asserted direct sum. -/
theorem selfDual_or_nearSelfDual {r : ℕ} (hr : 4 ≤ r) (U : BinaryCode (2*r))
    (hdim : Module.finrank (ZMod 2) U = r)
    (hacc : ∀ v, Accessible v → v ∈ dotOrthogonal U → v ∈ U) :
    U = dotOrthogonal U ∨
      let A0 := evenSpace (2*r) ⊓ dotOrthogonal U
      A0 ≤ U ∧ Module.finrank (ZMod 2) A0 = r-1 ∧
      ∃ u : BinaryVector (2*r), u ∈ U ∧ dot u u = 1 ∧
        U = A0 ⊔ Submodule.span (ZMod 2) {u} ∧
        Disjoint A0 (Submodule.span (ZMod 2) {u}) := by
  have ho : Module.finrank (ZMod 2) (dotOrthogonal U) = r := by
    rw [finrank_dotOrthogonal, hdim]; omega
  have hA := even_inter_orthogonal_le hr U hdim hacc
  by_cases he : dotOrthogonal U ≤ evenSpace (2*r)
  · left
    have hle : dotOrthogonal U ≤ U := by
      simpa only [inf_eq_right.mpr he] using hA
    exact (Submodule.eq_of_le_of_finrank_eq hle (ho.trans hdim.symm)).symm
  · right
    dsimp only
    have hd := finrank_evenSpace_inf_of_not_le (by omega : 0 < 2*r) (dotOrthogonal U) he
    rw [ho] at hd
    have hdA : Module.finrank (ZMod 2) ↥(evenSpace (2*r) ⊓ dotOrthogonal U) = r-1 := by omega
    have hn : ¬ U ≤ evenSpace (2*r) ⊓ dotOrthogonal U := by
      intro h
      have hh := Submodule.finrank_mono h
      rw [hdim, hdA] at hh
      omega
    change ¬ ∀ u, u ∈ U → u ∈ evenSpace (2*r) ⊓ dotOrthogonal U at hn
    push Not at hn
    obtain ⟨u, hu, hun⟩ := hn
    have hsup : U = (evenSpace (2*r) ⊓ dotOrthogonal U) ⊔ Submodule.span (ZMod 2) {u} := by
      symm
      apply Submodule.eq_of_le_of_finrank_eq
      · exact sup_le hA (Submodule.span_le.mpr (by simpa using hu))
      · rw [Submodule.finrank_sup_span_singleton hun, hdim]
        exact hd
    have hodd : dot u u ≠ 0 := by
      intro hzero
      have huperp : u ∈ dotOrthogonal U := by
        intro y hy
        rw [hsup] at hy
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
        change dot (a + c • u) u = 0
        rw [dot_add_left, dot_smul_left, hzero, mul_zero, add_zero, dot_comm]
        exact ha.2 u hu
      exact hun ⟨(mem_evenSpace u).mpr (by rwa [dot_ones]), huperp⟩
    have hodd1 : dot u u = 1 := by
      have hh : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact hh _ hodd
    exact ⟨hA, hdA, u, hu, hodd1, hsup, Submodule.disjoint_span_singleton_of_notMem hun⟩

end
end Holant.ReedMuller.AffineRadon
