import Holant.Proofs.FiniteGroups.Stabilization.FullRetainedDeck


namespace Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
attribute [local instance] Classical.propDecidable
variable {L : Type*} [Field L]

def RetainedUnary (F : SignatureFamily L) : Prop :=
  ∃ u : Signature L 1, (⟨1,u⟩ : AnySignature L) ∈ F ∧ u ≠ 0

theorem FactorTree.leaf_positive {f : AnySignature L} (t : FactorTree f) (hf : 0 < f.1)
    (a : AnySignature L) (ha : a ∈ t.leaves) : 0 < a.1 := by
  revert hf ha
  induction t with
  | leaf f hp =>
      intro hf ha
      have he : a = f := by simpa [FactorTree.leaves] using ha
      simpa only [he] using hf
  | split s ta tb iha ihb =>
      intro hf ha
      rcases Multiset.mem_add.mp ha with ha | hb
      · exact iha s.left_pos ha
      · exact ihb s.right_pos hb

/-- All-binary leaves are derived from minimum arity and the actual unary
obstruction, rather than supplied as a matching conclusion in disguise. -/
theorem card_leaf_binary {G : SignatureFamily L} (core : MinimumCore G)
    {m : ℕ} (hm : 0 < m) (hmin : m + 2 ≤ core.signature.1)
    (hu : ¬ RetainedUnary G) (f : Signature L m) (t : FactorTree (⟨m,f⟩ : AnySignature L))
    (hret : ∀ a ∈ t.leaves, a ∈ G) (a : AnySignature L) (ha : a ∈ t.leaves) : a.1 = 2 := by
  have hp := t.leaves_prime a ha
  have hlo := t.leaf_positive hm a ha
  have hhi := t.leaf_arity_le a ha
  change a.1 ≤ m at hhi
  have hnot3 : ¬ 3 ≤ a.1 := by
    intro h3
    have hc := core.minimum a (hret a ha) hp h3
    omega
  have hnot1 : a.1 ≠ 1 := by
    intro he
    apply hu
    rcases a with ⟨n,a⟩
    dsimp only at he
    subst n
    exact ⟨a, hret _ ha, hp.1⟩
  omega

theorem retained_card_matching {G : SignatureFamily L} (core : MinimumCore G)
    {m : ℕ} (hm : 0 < m) (hmin : m + 2 ≤ core.signature.1) (hu : ¬ RetainedUnary G)
    (f : Signature L m) (t : FactorTree (⟨m,f⟩ : AnySignature L))
    (hret : ∀ a ∈ t.leaves, a ∈ G) : MatchingOrZero (actualTransfers G) f :=
  t.matchingOrZero G hret (card_leaf_binary core hm hmin hu f t hret)

/-- Every literal member of the complete frozen deck is covered by the
constructed retained operation, including scalar-distinct raw cards. -/
theorem fullRetainedDeck_matching [NumberField L] {m : ℕ} (hm : 2 ≤ m)
    (F : SignatureFamily L) (hτ : ResidualTorsion F) (f : Signature L (m + 2))
    (core : MinimumCore (fullRetainedDeck F hτ f))
    (hmin : m + 2 ≤ core.signature.1) (hu : ¬ RetainedUnary (fullRetainedDeck F hτ f)) :
    ∀ g ∈ rawDeck F hτ f, MatchingOrZero (actualTransfers (fullRetainedDeck F hτ f)) g := by
  intro g hg
  rcases hg with hz | ⟨k, rfl⟩
  · exact Or.inl hz
  · by_cases hk : rawCard F hτ f k = 0
    · exact Or.inl hk
    · let i : FullDeckIndex F hτ f := .inr ⟨k,hk⟩
      exact retained_card_matching core (by omega) hmin hu _ (fullDeckRoot F hτ f i).2
        (fullRetainedDeck_leaf F hτ f i)

/-- A local obstruction alternative.  No source terminal theorem is invoked:
the first result is a concrete unary table, not a complexity conclusion. -/
theorem fullRetainedDeck_matching_or_obstruction [NumberField L] {m : ℕ} (hm : 2 ≤ m)
    (F : SignatureFamily L) (hτ : ResidualTorsion F) (f : Signature L (m + 2))
    (core : MinimumCore (fullRetainedDeck F hτ f)) :
    RetainedUnary (fullRetainedDeck F hτ f) ∨ core.signature.1 < m + 2 ∨
      ∀ g ∈ rawDeck F hτ f, MatchingOrZero (actualTransfers (fullRetainedDeck F hτ f)) g := by
  by_cases hu : RetainedUnary (fullRetainedDeck F hτ f)
  · exact Or.inl hu
  · by_cases hm' : core.signature.1 < m + 2
    · exact Or.inr (Or.inl hm')
    · exact Or.inr (Or.inr (fullRetainedDeck_matching hm F hτ f core (by omega) hu))

/-- A minimum for the concrete successor is constructed from the retained
old prime.  In particular the matching alternative never assumes that the
successor has already been classified or certified stable. -/
theorem fullRetainedDeck_minimum_outcome [NumberField L] {m : ℕ} (hm : 2 ≤ m)
    (F : SignatureFamily L) (hτ : ResidualTorsion F) (f : Signature L (m + 2))
    (old : MinimumCore F) (hcore : old.signature = ⟨m + 2,f⟩) :
    ∃ next : MinimumCore (fullRetainedDeck F hτ f),
      next.signature.1 ≤ old.signature.1 ∧
      (RetainedUnary (fullRetainedDeck F hτ f) ∨ next.signature.1 < old.signature.1 ∨
        ∀ g ∈ rawDeck F hτ f, MatchingOrZero (actualTransfers (fullRetainedDeck F hτ f)) g) := by
  have hr := fullRetainedDeck_retains F hτ f
  obtain ⟨next⟩ := exists_minimumCore (fullRetainedDeck F hτ f)
    ⟨old.signature, hr old.retained, old.prime, old.nonbinary⟩
  refine ⟨next, MinimumCore.arity_nonincrease hr old next, ?_⟩
  have hn : old.signature.1 = m + 2 := congrArg Sigma.fst hcore
  rw [hn]
  exact fullRetainedDeck_matching_or_obstruction hm F hτ f next

/-- At an unchanged complete group and minimum arity, the constructed family
is finite and factor-saturated, retains the actual representatives and all
nonzero literal cards, and its entire frozen complete deck is zero or a
literal representative matching.  The missing unary dispatch is explicit.
Turing equivalence is deliberately not part of this mathematical theorem. -/
theorem unchanged_fullRetainedDeck_stable [NumberField L] {m : ℕ} (hm : 2 ≤ m)
    (F : SignatureFamily L) (hF : F.Finite) (hsat : FactorSaturated F)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2))
    (old : MinimumCore F) (hcore : old.signature = ⟨m + 2,f⟩)
    (next : MinimumCore (fullRetainedDeck F hτ f))
    (hmin : next.signature.1 = old.signature.1)
    (hG : ResidualTorsion (fullRetainedDeck F hτ f))
    (hgroup : completeGroup (fullRetainedDeck F hτ f) hG = completeGroup F hτ)
    (hu : ¬ RetainedUnary (fullRetainedDeck F hτ f)) :
    (fullRetainedDeck F hτ f).Finite ∧ FactorSaturated (fullRetainedDeck F hτ f) ∧
      F ⊆ fullRetainedDeck F hτ f ∧
      (∀ q : completeGroup F hτ,
        (⟨2,binarySignature (actualRepresentative F hτ q)⟩ : AnySignature L) ∈ fullRetainedDeck F hτ f) ∧
      (∀ B, ActualNonsingular (fullRetainedDeck F hτ f) B →
        ∃ q : completeGroup F hτ, ∃ c : L, c ≠ 0 ∧ B = c • actualRepresentative F hτ q) ∧
      ∀ g ∈ rawDeck F hτ f, g = 0 ∨ RepresentativeMatching (fullRetainedDeck F hτ f) hG g := by
  refine ⟨fullRetainedDeck_finite F hF hτ f, fullRetainedDeck_saturated F hsat hτ f,
    fullRetainedDeck_retains F hτ f, fullRetainedDeck_representative F hτ f,
    (frozen_representatives_cover_retained (fullRetainedDeck_retains F hτ f) hτ hG hgroup).2, ?_⟩
  intro g hg
  apply (matchingOrZero_iff_representatives _ hG g).mp
  apply fullRetainedDeck_matching hm F hτ f next _ hu g hg
  have hn : old.signature.1 = m + 2 := congrArg Sigma.fst hcore
  omega

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
