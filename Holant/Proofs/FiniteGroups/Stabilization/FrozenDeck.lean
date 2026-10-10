import Holant.Proofs.FiniteGroups.Stabilization.Representatives
import Holant.Proofs.FiniteGroups.Stabilization.CanonicalKeys
import Holant.Proofs.FiniteGroups.Stabilization.QueueExhaustion
import Holant.Proofs.FiniteGroups.Stabilization.RetainedBatch
import Holant.Dihedral.CompatibleClosure.ActualReindex


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.OpenNetworkComposition
noncomputable section
attribute [local instance] Classical.propDecidable
variable {L : Type*} [Field L]

def orientBinary (reverse : Bool) (B : Binary (K := L)) : Binary (K := L) :=
  if reverse then B.transpose else B

theorem realizes_orientBinary {F : SignatureFamily L} {B : Binary (K := L)}
    (hB : Gadget.Realizes F .disequality (binarySignature B)) (reverse : Bool) :
    Gadget.Realizes F .disequality (binarySignature (orientBinary reverse B)) := by
  cases reverse
  · exact hB
  · have he : binarySignature B.transpose =
        Tensor.reindex (Equiv.swap (0 : Fin 2) 1).symm (binarySignature B) := by
      funext x
      simp [binarySignature, Tensor.reindex, Equiv.swap_apply_def]
    change Gadget.Realizes F .disequality (binarySignature B.transpose)
    rw [he]
    exact Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ hB _

abbrev RawCardKey (m : ℕ) (H : Type*) :=
  (Fin (m + 2) → Option (H × Bool)) × Equiv.Perm (Fin (m + 2)) × H × Bool

def dressAt {n : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L n) (δ : Fin n → Option (completeGroup F hτ × Bool)) (i : Fin n) :
    Signature L n :=
  match δ i with
  | none => f
  | some (q, reverse) =>
      spliceTensor f (binarySignature (orientBinary reverse (actualRepresentative F hτ q))) i

theorem dressAt_actual {n : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L n) (hf : Gadget.Realizes F .disequality f)
    (δ : Fin n → Option (completeGroup F hτ × Bool)) (i : Fin n) :
    Gadget.Realizes F .disequality (dressAt F hτ f δ i) := by
  unfold dressAt
  cases δ i with
  | none => exact hf
  | some q =>
      exact realizes_splice F f _ hf
        (realizes_orientBinary (actualRepresentative_actual F hτ q.1).1 q.2) i

def dress {n : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L n) (δ : Fin n → Option (completeGroup F hτ × Bool)) : Signature L n :=
  (List.finRange n).foldl (fun g i => dressAt F hτ g δ i) f

theorem dress_actual {n : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L n) (hf : Gadget.Realizes F .disequality f)
    (δ : Fin n → Option (completeGroup F hτ × Bool)) :
    Gadget.Realizes F .disequality (dress F hτ f δ) := by
  suffices h : ∀ is : List (Fin n), ∀ g : Signature L n,
      Gadget.Realizes F .disequality g →
      Gadget.Realizes F .disequality (is.foldl (fun q i => dressAt F hτ q δ i) g) from
    h _ f hf
  intro is
  induction is with
  | nil => exact fun g hg => hg
  | cons i is ih => exact fun g hg => ih _ (dressAt_actual F hτ g hg δ i)

/-- Reindexing places the ordered deleted pair in the first two slots and
retains the residual port order.  All such choices are present in the key. -/
def rawCard {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (k : RawCardKey m (completeGroup F hτ)) : Signature L m :=
  Signature.contract (X * orientBinary k.2.2.2 (actualRepresentative F hτ k.2.2.1) * X)
    (Tensor.reindex k.2.1.symm (dress F hτ f k.1))

def rawDeck {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) : Set (Signature L m) := {0} ∪ Set.range (rawCard F hτ f)

def canonicalDeck {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) : Set (Signature L m) := canonicalKey '' rawDeck F hτ f

theorem rawDeck_finite [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) : (rawDeck F hτ f).Finite := by
  letI := completeGroup_finite F hτ
  exact (Set.finite_singleton _).union (Set.finite_range _)

theorem canonicalDeck_finite [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) : (canonicalDeck F hτ f).Finite :=
  (rawDeck_finite F hτ f).image canonicalKey

abbrev CanonicalToken {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) := {g : Signature L m // g ∈ canonicalDeck F hτ f ∧ g ≠ 0}

theorem token_has_raw_card {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (t : CanonicalToken F hτ f) :
    ∃ k : RawCardKey m (completeGroup F hτ),
      canonicalKey (rawCard F hτ f k) = t.1 ∧ rawCard F hτ f k ≠ 0 := by
  obtain ⟨g, hg, he⟩ := t.2.1
  have hn : g ≠ 0 := by intro hz; apply t.2.2; rw [← he, hz, canonicalKey_zero]
  rcases hg with hz | ⟨k, rfl⟩
  · exact False.elim (hn hz)
  · exact ⟨k, he, hn⟩

def selectedRawCard {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (t : CanonicalToken F hτ f) : Signature L m :=
  rawCard F hτ f (token_has_raw_card F hτ f t).choose

theorem selectedRawCard_key {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (t : CanonicalToken F hτ f) :
    canonicalKey (selectedRawCard F hτ f t) = t.1 :=
  (token_has_raw_card F hτ f t).choose_spec.1

theorem selectedRawCard_nonzero {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (t : CanonicalToken F hτ f) : selectedRawCard F hτ f t ≠ 0 :=
  (token_has_raw_card F hτ f t).choose_spec.2

/-- The discarded scalar is explicit, nonzero, and reconstructs the original
card.  It is never silently turned into a resource normalization. -/
theorem selectedRawCard_scalar {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (t : CanonicalToken F hτ f) :
    ∃ c : L, c ≠ 0 ∧ selectedRawCard F hτ f t = c • t.1 := by
  let g := selectedRawCard F hτ f t
  have hg : g ≠ 0 := selectedRawCard_nonzero F hτ f t
  refine ⟨g (firstWord g hg), firstWord_nonzero g hg, ?_⟩
  exact (recover_from_key g hg).trans (congrArg (fun z => g (firstWord g hg) • z)
    (selectedRawCard_key F hτ f t))

def selectedCardTree {m : ℕ} (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) (t : CanonicalToken F hτ f) : TreeOccurrence L :=
  ⟨⟨m, selectedRawCard F hτ f t⟩,
    (exists_factorTree _ (selectedRawCard_nonzero F hτ f t)).some⟩

theorem canonicalToken_finite [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) : Finite (CanonicalToken F hτ f) :=
  ((canonicalDeck_finite F hτ f).subset (fun _ h => h.1)).to_subtype

def canonicalUniverse [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) : Finset (CanonicalToken F hτ f) := by
  letI := canonicalToken_finite F hτ f
  letI := Fintype.ofFinite (CanonicalToken F hτ f)
  exact Finset.univ

theorem mem_canonicalUniverse [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) (t : CanonicalToken F hτ f) :
    t ∈ canonicalUniverse F hτ f := by simp [canonicalUniverse]

def retainFrozenDeck [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) : SignatureFamily L :=
  retainBatch F (canonicalUniverse F hτ f) (selectedCardTree F hτ f)

theorem retainFrozenDeck_properties [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hF : F.Finite) (hsat : FactorSaturated F) (hτ : ResidualTorsion F)
    (f : Signature L (m + 2)) :
    (retainFrozenDeck F hτ f).Finite ∧ F ⊆ retainFrozenDeck F hτ f ∧
      FactorSaturated (retainFrozenDeck F hτ f) :=
  ⟨retainBatch_finite hF _ _, retainBatch_retains F _ _, retainBatch_saturated hsat _ _⟩

theorem frozen_leaf_retained [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) (t : CanonicalToken F hτ f)
    (a : AnySignature L) (ha : a ∈ (selectedCardTree F hτ f t).2.leaves) :
    a ∈ retainFrozenDeck F hτ f :=
  retainBatch_leaf F _ _ (mem_canonicalUniverse F hτ f t) ha

/-- The smaller-core exit uses an actual leaf of a selected proper card;
its retained membership and two-port arity loss are supplied internally. -/
theorem frozen_leaf_smaller [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) (core : MinimumCore F)
    (hcore : core.signature.1 = m + 2) (next : MinimumCore (retainFrozenDeck F hτ f))
    (t : CanonicalToken F hτ f) (a : AnySignature L)
    (ha : a ∈ (selectedCardTree F hτ f t).2.leaves) (hnb : 3 ≤ a.1) :
    next.signature.1 < core.signature.1 :=
  smaller_core_of_card_leaf core next (selectedCardTree F hτ f t).1 hcore.symm
    (selectedCardTree F hτ f t).2 a ha (frozen_leaf_retained F hτ f t a ha) hnb

/-- The queue is constructed from the finite displayed deck and its exact
stored trees; no finite-universe or queue-progress premise is supplied. -/
theorem canonicalDeck_queue_exhausts [NumberField L] {m : ℕ} (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (f : Signature L (m + 2)) :
    ∃ q : FrozenQueue L (canonicalUniverse F hτ f),
      FrozenQueue.Runs (FrozenQueue.initial (canonicalUniverse F hτ f) (selectedCardTree F hτ f)) q ∧
      q.todo = ∅ := by
  classical
  exact FrozenQueue.initial_exhausts _ _

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
