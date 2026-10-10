import Holant.ReedMuller.FlatNetwork.GenerationLift
import Holant.ReedMuller.FlatNetwork.GenerationReduction

/-! Algebraic converse of Lemma 7.14: every binary self-dual code is generated
from adjacent repetition pairs by a finite program of actual weight-four
transvections and coordinate permutations. The explicit bound is quadratic. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Once the first pair word belongs to a self-dual code, the first two
coordinates of every codeword agree. -/
theorem equal_first_pair_of_mem (D : BinaryCode (n+2)) (hD : SelfDual D)
    (hp : pairWord n ∈ D) (x : BinaryVector (n+2)) (hx : x ∈ D) : x 0 = x 1 := by
  apply (add_eq_zero_iff _ _).mp
  simpa only [dot_pairWord] using (hD (pairWord n)).mp hp x hx

/-- Splitting off a present adjacent repetition pair recovers the code
exactly, not merely its dimension or an abstract isomorphic copy. -/
theorem eq_pairExtension_projection (D : BinaryCode (n+2)) (hD : SelfDual D)
    (hp : pairWord n ∈ D) : D = pairExtension (equalProjection D) := by
  ext x
  constructor
  · intro hx
    have he := equal_first_pair_of_mem D hD hp x hx
    exact ⟨he, dropTwo_mem_of_equal D x hx he⟩
  · rintro ⟨he, hx⟩
    apply (hD x).mpr
    intro y hy
    have hey := equal_first_pair_of_mem D hD hp y hy
    have hyp := dropTwo_mem_of_equal D y hy hey
    have hh := (equalProjection_selfDual D hD (dropTwo x)).mp hx (dropTwo y) hyp
    calc
      dot x y = dot (prepend (x 0) (dropTwo x)) (prepend (y 0) (dropTwo y)) := by
        rw [prepend_dropTwo x he, prepend_dropTwo y hey]
      _ = dot (dropTwo x) (dropTwo y) := dot_prepend _ _ _ _
      _ = 0 := hh

/-- Universal generation with an explicit quadratic number of primitives.
Each primitive is either an arbitrary coordinate permutation or the literal
map `x ↦ x + dot x s • s` with `binaryWeight s = 4`. -/
theorem selfDual_generation (n : ℕ) (D : BinaryCode n) (hD : SelfDual D) :
    ∃ p : GenerationProgram n, p.run (standardPairs n) = D ∧ p.length ≤ n*n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    refine ⟨[], ?_, by simp⟩
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    constructor
    · intro _
      rw [hx]
      exact D.zero_mem
    · intro _
      change x ∈ (⊥ : BinaryCode 0)
      rw [hx]
      exact Submodule.zero_mem _
  | one =>
    have h := selfDual_arity_even D hD
    obtain ⟨a, ha⟩ := h
    omega
  | more n ih _ =>
    obtain ⟨q, hqbound, hqpair⟩ := exists_pair_reduction D hD
    have hqself := q.preserves_selfDual D hD
    have hsplit := eq_pairExtension_projection (q.run D) hqself hqpair
    obtain ⟨p, hp, hpbound⟩ := ih (equalProjection (q.run D))
      (equalProjection_selfDual (q.run D) hqself)
    refine ⟨q.inverse ++ p.lift, ?_, ?_⟩
    · rw [GenerationProgram.run_append]
      change q.inverse.run (p.lift.run (pairExtension (standardPairs n))) = D
      rw [GenerationProgram.lift_run, hp, ← hsplit, GenerationProgram.run_inverse]
    · simp only [List.length_append, GenerationProgram.inverse_length, GenerationProgram.lift_length]
      nlinarith

/-- Source arity convention: at most `4 k²` gates generate any self-dual
code on `2k` ports from the standard `k` adjacent repetition pairs. -/
theorem selfDual_generation_quadratic (k : ℕ) (D : BinaryCode (2*k)) (hD : SelfDual D) :
    ∃ p : GenerationProgram (2*k), p.run (standardPairs (2*k)) = D ∧
      p.length ≤ 4*k^2 := by
  obtain ⟨p, hp, hb⟩ := selfDual_generation (2*k) D hD
  refine ⟨p, hp, ?_⟩
  nlinarith

/-- The generating program acts on actual words: its image of the standard
pair code is precisely the requested code. -/
theorem selfDual_generation_words (k : ℕ) (D : BinaryCode (2*k)) (hD : SelfDual D) :
    ∃ p : GenerationProgram (2*k), p.length ≤ 4*k^2 ∧
      ∀ x, x ∈ D ↔ ∃ y ∈ standardPairs (2*k), p.word y = x := by
  obtain ⟨p, hp, hb⟩ := selfDual_generation_quadratic k D hD
  refine ⟨p, hb, ?_⟩
  intro x
  rw [← hp]
  exact p.run_image _ x

end
end Holant.ReedMuller.FlatNetwork
