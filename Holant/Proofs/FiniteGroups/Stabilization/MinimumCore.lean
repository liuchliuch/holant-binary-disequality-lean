import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

noncomputable section
variable {L : Type*} [Field L]

structure MinimumCore (F : SignatureFamily L) where
  signature : AnySignature L
  retained : signature ∈ F
  prime : Prime signature
  nonbinary : 3 ≤ signature.1
  minimum : ∀ g ∈ F, Prime g → 3 ≤ g.1 → signature.1 ≤ g.1

theorem exists_minimumCore (F : SignatureFamily L)
    (hne : ∃ f ∈ F, Prime f ∧ 3 ≤ f.1) : Nonempty (MinimumCore F) := by
  classical
  have hn : ∃ n : ℕ, ∃ f ∈ F, Prime f ∧ 3 ≤ f.1 ∧ f.1 = n := by
    obtain ⟨f, hf, hp, h3⟩ := hne
    exact ⟨f.1, f, hf, hp, h3, rfl⟩
  obtain ⟨f, hf, hp, h3, he⟩ := Nat.find_spec hn
  refine ⟨⟨f, hf, hp, h3, ?_⟩⟩
  intro g hg hgp hg3
  rw [he]
  exact Nat.find_min' hn ⟨g, hg, hgp, hg3, rfl⟩

/-- Retention, not a new arity monotonicity premise, supplies nonincrease. -/
theorem MinimumCore.arity_nonincrease {F G : SignatureFamily L} (hFG : F ⊆ G)
    (f : MinimumCore F) (g : MinimumCore G) : g.signature.1 ≤ f.signature.1 :=
  g.minimum f.signature (hFG f.retained) f.prime f.nonbinary

theorem FactorTree.leaf_arity_le {f : AnySignature L} (t : FactorTree f)
    (a : AnySignature L) (ha : a ∈ t.leaves) : a.1 ≤ f.1 := by
  induction t with
  | leaf f hp =>
      have he : a = f := by simpa only [FactorTree.leaves, Multiset.mem_singleton] using ha
      subst a
      exact le_rfl
  | split s ta tb iha ihb =>
      rcases Multiset.mem_add.mp ha with ha | hb
      · exact (iha ha).trans s.left_lt.le
      · exact (ihb hb).trans s.right_lt.le

/-- A retained nonbinary leaf of a proper card forces a strictly smaller
minimum core.  The card's arity drop is a literal port-count premise. -/
theorem smaller_core_of_card_leaf {F G : SignatureFamily L}
    (f : MinimumCore F) (g : MinimumCore G) (card : AnySignature L)
    (hcard : card.1 + 2 = f.signature.1) (tree : FactorTree card)
    (leaf : AnySignature L) (hleaf : leaf ∈ tree.leaves)
    (hretained : leaf ∈ G) (hnb : 3 ≤ leaf.1) :
    g.signature.1 < f.signature.1 := by
  have hmin := g.minimum leaf hretained (tree.leaves_prime leaf hleaf) hnb
  have hle := tree.leaf_arity_le leaf hleaf
  omega

/-- The precise logical branch before applying the external odd theorem.
No hardness proof is manufactured from an odd arity witness here. -/
theorem card_leaf_odd_or_even_smaller {F G : SignatureFamily L}
    (f : MinimumCore F) (g : MinimumCore G) (card : AnySignature L)
    (hcard : card.1 + 2 = f.signature.1) (tree : FactorTree card)
    (leaf : AnySignature L) (hleaf : leaf ∈ tree.leaves)
    (hretained : leaf ∈ G) (hnb : 3 ≤ leaf.1) :
    Odd leaf.1 ∨ (Even leaf.1 ∧ g.signature.1 < f.signature.1) := by
  rcases Nat.even_or_odd leaf.1 with he | ho
  · exact Or.inr ⟨he, smaller_core_of_card_leaf f g card hcard tree leaf hleaf hretained hnb⟩
  · exact Or.inl ho

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
