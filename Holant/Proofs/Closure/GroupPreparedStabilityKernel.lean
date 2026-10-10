import Holant.Proofs.Closure.ContinuationTransport
import Holant.Proofs.Closure.OccurrenceCurrent

/-! FINAL minimality applies to the retained factor trees of any earlier
actual batch, even when that selected prime was not minimum at its visit.
Same-group representative transport then proves its CURRENT regenerated deck.
This kernel lemma is instantiated by actual group-preparation receipts. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GroupPreparedStability
open Holant Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Certificates.MatchingContractionClosure
variable {L : Type*} [Field L]

/-- Every saved prime leaf of the old proper card lies in FINAL Q. Its
FINAL actual minimum and absence of unary force those leaves to be binary. -/
theorem retained_batch_matching_in_final [NumberField L] {m : ℕ} (hm : 2 ≤ m)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2))
    (Q : SignatureFamily L) (saved : fullRetainedDeck F torsion f ⊆ Q)
    (core : MinimumCore Q) (minimum : m+2 ≤ core.signature.1)
    (noUnary : ¬ RetainedUnary Q) :
    ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers Q) g := by
  intro g hg
  rcases hg with hz | ⟨k,rfl⟩
  · exact Or.inl hz
  · by_cases hk : rawCard F torsion f k = 0
    · exact Or.inl hk
    · let i : FullDeckIndex F torsion f := .inr ⟨k,hk⟩
      exact retained_card_matching core (by omega) minimum noUnary _
        (fullDeckRoot F torsion f i).2
        (fun a ha => saved (fullRetainedDeck_leaf F torsion f i a ha))

/-- Actual final-group provenance is necessary here. Group growth does not
satisfy this premise; the generated-group producer establishes it only for
visits after its last genuine strict-growth restart. -/
theorem regenerated_batch_matching_in_final [NumberField L] {m : ℕ} (hm : 2 ≤ m)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2))
    (Q : SignatureFamily L) (saved : fullRetainedDeck F torsion f ⊆ Q)
    (finalTorsion : ResidualTorsion Q)
    (sameGroup : completeGroup Q finalTorsion = completeGroup F torsion)
    (core : MinimumCore Q) (minimum : m+2 ≤ core.signature.1)
    (noUnary : ¬ RetainedUnary Q) :
    ∀ g ∈ rawDeck Q finalTorsion f, MatchingOrZero (actualTransfers Q) g :=
  ContinuationTransport.regenerated_matching
    ((fullRetainedDeck_retains F torsion f).trans saved)
    torsion finalTorsion sameGroup f
    (retained_batch_matching_in_final hm F torsion f Q saved core minimum noUnary)

/-- A true prime root cannot have a proper split in its exact saved tree. -/
theorem prime_tree_address {f : AnySignature L} (prime : Prime f) (tree : FactorTree f) :
    ∃ address : Occurrences.Address tree, (Occurrences.leaf tree address).1 = f := by
  cases tree with
  | leaf f hp => exact ⟨(),rfl⟩
  | split split left right => exact (prime.2 ⟨_,_,⟨split⟩⟩).elim

/-- Every retained prime value, including an arbitrary FINAL minimum, is an
actual leaf occurrence of one of the palette's once-saved trees. -/
theorem current_prime_occurrence {s : ℕ} {a : ℕ → ℕ}
    (G : (i : Fin s) → Signature Holant.Tractable.AlgebraicComplex (a i.val))
    (P : Palette G) (q : AnySignature (OI.K G)) (retained : q ∈ P.family) (prime : Prime q) :
    ∃ o : CurrentOccurrences.Id G P, (CurrentOccurrences.savedLeaf G P o).1 = q := by
  obtain ⟨i,hi⟩ := retained
  have hp : Prime (⟨P.arity i.val,P.table i⟩ : AnySignature (OI.K G)) := by simpa only [hi] using prime
  obtain ⟨address,he⟩ := prime_tree_address hp (P.trees i)
  exact ⟨⟨i,address⟩,he.trans hi⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GroupPreparedStability
end
