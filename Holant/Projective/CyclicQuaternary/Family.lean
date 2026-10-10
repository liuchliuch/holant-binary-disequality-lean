import Holant.Projective.CyclicQuaternary.Blocks

/-! Full three-complement coordinate classification in manuscript Lemma 7.2,
including its converse and mutual exclusivity. Scalars remain in the actual
coefficient field, and zero central blocks are retained in both alternatives. -/
noncomputable section
namespace Holant.Projective.CyclicQuaternary
open CyclicPhasePencil
variable {K : Type*} [Field K]

/-- I={01,02,03}; each value lists (x_I,x_complement) in that fixed order. -/
abbrev Blocks (K : Type*) := Fin 3 → K × K

def BlockRelations (m : ℕ) (p t : K) (xs : Blocks K) : Prop :=
  ∀ i, BlockCondition m p t (xs i).1 (xs i).2

def NonzeroFamily (m : ℕ) (p t : K) (xs : Blocks K) : Prop :=
  p≠0 ∧ t≠0 ∧ (t/p)^m=1 ∧ ∀ i, NonzeroBlock m p t (xs i).1 (xs i).2

def ZeroFamily (m : ℕ) (p t : K) (xs : Blocks K) : Prop :=
  p=0 ∧ t=0 ∧ ∀ i, ZeroBlock m (xs i).1 (xs i).2

def PhaseFamilies (m : ℕ) (p t : K) (xs : Blocks K) : Prop :=
  ∀ i, MatrixSamples m p (xs i).1 (xs i).2 t ∧ MatrixSamples m p (xs i).2 (xs i).1 t

/-- Exactly the two source coordinate families, with no missing zero patterns. -/
theorem blockRelations_iff {m : ℕ} (hm : 0<m) (p t : K) (xs : Blocks K) :
    BlockRelations m p t xs ↔ NonzeroFamily m p t xs ∨ ZeroFamily m p t xs := by
  constructor
  · intro h
    by_cases hp : p=0
    · have ht := (endpoint_zero_iff hm p t (xs 0).1 (xs 0).2 (h 0)).mp hp
      right
      refine ⟨hp,ht,?_⟩
      intro i
      exact zero_block hm _ _ (by simpa only [hp,ht] using h i)
    · have ht : t≠0 := fun ht => hp ((endpoint_zero_iff hm p t (xs 0).1 (xs 0).2 (h 0)).mpr ht)
      left
      exact ⟨hp,ht,(nonzero_block hm p t _ _ hp ht (h 0)).1,
        fun i => (nonzero_block hm p t _ _ hp ht (h i)).2⟩
  · rintro (⟨hp,ht,hphase,h⟩ | ⟨rfl,rfl,h⟩) i
    · exact block_of_nonzero hm p t _ _ hp hphase (h i)
    · exact block_of_zero hm _ _ (h i)

/-- The two alternatives cannot both hold, as asserted by "exactly one". -/
theorem families_disjoint (m : ℕ) (p t : K) (xs : Blocks K) :
    ¬(NonzeroFamily m p t xs ∧ ZeroFamily m p t xs) := by
  rintro ⟨h,h'⟩
  exact h.1 h'.1

/-- In particular, exactly one nonzero endpoint is impossible. -/
theorem no_mixed_endpoints {m : ℕ} (hm : 0<m) (p t : K) (xs : Blocks K)
    (h : BlockRelations m p t xs) : (p=0 ↔ t=0) :=
  endpoint_zero_iff hm p t (xs 0).1 (xs 0).2 (h 0)

/-- Stronger complex-coefficient version of the entire phase-family equivalence. -/
theorem phase_families_complex {m : ℕ} (hm : 3≤m) (p t : ℂ) (xs : Blocks ℂ) :
    PhaseFamilies m p t xs ↔ NonzeroFamily m p t xs ∨ ZeroFamily m p t xs := by
  rw [← blockRelations_iff (by omega)]
  unfold PhaseFamilies BlockRelations BlockCondition
  simp only [← cyclic_phase_pencil hm]

/-- Lemma 7.2 coordinate classification and converse over the exact source field.
Both complementary deletions and every finite cyclic phase are quantified. -/
theorem phase_families_algebraic {m : ℕ} (hm : 3≤m)
    (p t : Holant.Tractable.AlgebraicComplex) (xs : Blocks Holant.Tractable.AlgebraicComplex) :
    PhaseFamilies m p t xs ↔ NonzeroFamily m p t xs ∨ ZeroFamily m p t xs := by
  rw [← blockRelations_iff (by omega)]
  unfold PhaseFamilies BlockRelations BlockCondition
  simp only [← cyclic_phase_pencil_algebraic hm]

end Holant.Projective.CyclicQuaternary
