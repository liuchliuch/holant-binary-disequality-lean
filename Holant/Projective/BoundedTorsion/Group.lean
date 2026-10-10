import Holant.Certificates.MatchingContractionClosure.GroupAlgebra
import Mathlib.GroupTheory.OrderOfElement

/-! The subgroup step of source Lemma 5.2.  Positive projective powers,
not a finiteness or uniform-exponent assumption, supply identity and inverses.
The arithmetic and linear-group finiteness steps are separate obligations. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {K : Type*} [Field K]

/-- A positive power of this literal matrix is a nonzero scalar identity. -/
def ProjectivelyFinite (T : Binary (K := K)) : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∃ c : K, c ≠ 0 ∧ T ^ r = c • (1 : Binary)

theorem ProjectivelyFinite.smul {T : Binary (K := K)}
    (hT : ProjectivelyFinite T) {c : K} (hc : c ≠ 0) :
    ProjectivelyFinite (c • T) := by
  obtain ⟨r, hr, d, hd, heq⟩ := hT
  refine ⟨r, hr, c ^ r * d, mul_ne_zero (pow_ne_zero _ hc) hd, ?_⟩
  rw [smul_pow, heq, smul_smul]

theorem positive_power_mem {G : Set (Binary (K := K))}
    (hmul : ∀ U ∈ G, ∀ V ∈ G, U * V ∈ G)
    {T : Binary (K := K)} (hT : T ∈ G) {r : ℕ} (hr : 0 < r) : T ^ r ∈ G := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  induction s with
  | zero => simpa using hT
  | succ s ih => simpa only [pow_succ] using hmul _ (ih (Nat.succ_pos _)) _ hT

/-- A nonempty scalar-saturated multiplicative torsion set already satisfies
the project's literal projective-matrix-group interface. -/
theorem projectiveMatrixGroup_of_torsion {G : Set (Binary (K := K))}
    (hne : G.Nonempty)
    (hmul : ∀ U ∈ G, ∀ V ∈ G, U * V ∈ G)
    (hscale : ∀ U ∈ G, ∀ c : K, c ≠ 0 → c • U ∈ G)
    (htorsion : ∀ T ∈ G, ProjectivelyFinite T) : ProjectiveMatrixGroup G := by
  have hone : (1 : Binary (K := K)) ∈ G := by
    obtain ⟨T, hT⟩ := hne
    obtain ⟨r, hr, c, hc, heq⟩ := htorsion T hT
    have h := hscale _ (positive_power_mem hmul hT hr) c⁻¹ (inv_ne_zero hc)
    simpa only [heq, smul_smul, inv_mul_cancel₀ hc, one_smul] using h
  refine ⟨hone, hmul, ?_, hscale⟩
  intro T hT
  obtain ⟨r, hr, c, hc, heq⟩ := htorsion T hT
  have hp : T ^ (r - 1) ∈ G := by
    by_cases hz : r - 1 = 0
    · simpa only [hz, pow_zero] using hone
    · exact positive_power_mem hmul hT (Nat.pos_of_ne_zero hz)
  refine ⟨c⁻¹ • T ^ (r - 1), hscale _ hp _ (inv_ne_zero hc), ?_, ?_⟩
  · rw [Matrix.mul_smul, ← pow_succ', Nat.sub_add_cancel hr, heq,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rw [Matrix.smul_mul, ← pow_succ, Nat.sub_add_cancel hr, heq,
      smul_smul, inv_mul_cancel₀ hc, one_smul]

end
end Holant.Projective.BoundedTorsion
