import Holant.Projective.CyclicQuaternary.Contraction

/-! Manuscript Lemma 7.2: exact classification of every normalized cyclic
contraction of an even four-port Walsh table, and the full converse. The input
may be any algebraic table, a stronger statement than restricting to realized
tables. No analytic scalar normalization is treated as a gadget construction. -/
noncomputable section
namespace Holant.Projective.CyclicQuaternary
open Holant.Tractable

/-- Full literal-table equivalence from Lemma 7.2. All three complementary
pairs, both deletions, both residual orders, and every actual root are included. -/
theorem cyclic_quaternary_phase_family {m : ℕ} (hm : 3≤m)
    (q : Signature AlgebraicComplex 4) (heven : EvenSupported q) :
    AllPhaseCards m q ↔
      NonzeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q) ∨
      ZeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q) := by
  rw [allPhaseCards_iff m q heven]
  exact phase_families_algebraic hm _ _ _

/-- The source's "exactly one" is an explicit disjointness conclusion. -/
theorem cyclic_quaternary_exactly_one {m : ℕ} (hm : 3≤m)
    (q : Signature AlgebraicComplex 4) (heven : EvenSupported q) (hcards : AllPhaseCards m q) :
    (NonzeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q) ∨
      ZeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q)) ∧
    ¬(NonzeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q) ∧
      ZeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q)) :=
  ⟨(cyclic_quaternary_phase_family hm q heven).mp hcards,families_disjoint _ _ _ _⟩

/-- No physical phase family can have exactly one nonzero endpoint coordinate. -/
theorem cyclic_quaternary_endpoints {m : ℕ} (hm : 3≤m)
    (q : Signature AlgebraicComplex 4) (heven : EvenSupported q) (hcards : AllPhaseCards m q) :
    endpoint0 q=0 ↔ endpoint1 q=0 := by
  rcases (cyclic_quaternary_phase_family hm q heven).mp hcards with h | h
  · simp [h.1,h.2.1]
  · simp [h.1,h.2.1]

/-- The converse is for every even table with the stated coordinates, including
all zero central blocks and the all-zero tensor. -/
theorem cyclic_quaternary_converse {m : ℕ} (hm : 3≤m)
    (q : Signature AlgebraicComplex 4) (heven : EvenSupported q)
    (hfamily : NonzeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q) ∨
      ZeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q)) : AllPhaseCards m q :=
  (cyclic_quaternary_phase_family hm q heven).mpr hfamily

/-- The same tensor-level statement also holds over all complex coefficients. -/
theorem cyclic_quaternary_phase_family_complex {m : ℕ} (hm : 3≤m)
    (q : Signature ℂ 4) (heven : EvenSupported q) :
    AllPhaseCards m q ↔
      NonzeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q) ∨
      ZeroFamily m (endpoint0 q) (endpoint1 q) (coordinates q) := by
  rw [allPhaseCards_iff m q heven]
  exact phase_families_complex hm _ _ _

end Holant.Projective.CyclicQuaternary
