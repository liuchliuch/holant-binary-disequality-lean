import Holant.Proofs.Closure.GeneratedGroupWorklistAccess
import Holant.Proofs.Closure.FrontierCurrentClosure

/-! Exact lower-arity coverage of every prepared CURRENT raw card.  A nonzero
card uses the root and all branch addresses copied from its own saved event.
The final group transport changes only the explicit original-field scalar.
Preparation supplies these leaves and charged access; it does not assert that
all of those genuinely lower leaves are binary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentCoverage
open Holant Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.StableClosureV2
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {S T : GeneratedGroupWorklist.Active G base}
variable {h : GeneratedGroupWorklist.Trace G base S T}
variable {o : CurrentOccurrences.Id G T.source.palette}
variable (r : GeneratedGroupWorklist.PreparationReceipt G base h o)
variable (proper : 4 ≤ (CurrentOccurrences.savedLeaf G T.source.palette o).1.1)

abbrev input := (r.higherData G base proper).input
abbrev oldTorsion := (r.higherData G base proper).ready.torsion
abbrev Key := RawCardKey (input G base r proper).m
  (completeGroup T.source.palette.family T.ready.torsion)
abbrev current (k : Key G base r proper) := rawCard T.source.palette.family
  T.ready.torsion (input G base r proper).signature k
abbrev transport (k : Key G base r proper) :=
  GeneratedDeckTransport.currentCard G r.before.source.palette T.source.palette r.sourceRetained
    (oldTorsion G base r proper) T.ready.torsion r.currentGroup
    (input G base r proper).signature k
abbrev oldFullKey (k : Key G base r proper) (nonzero : current G base r proper k ≠ 0) :=
  GeneratedDeckTransport.oldFullKey G r.before.source.palette T.source.palette r.sourceRetained
    (oldTorsion G base r proper) T.ready.torsion r.currentGroup
    (input G base r proper).signature k nonzero
abbrev oldRoot (k : Key G base r proper) (nonzero : current G base r proper k ≠ 0) :=
  fullDeckRoot r.before.source.palette.family (oldTorsion G base r proper)
    (input G base r proper).signature (oldFullKey G base r proper k nonzero)

def copiedRoot (k : Key G base r proper) (nonzero : current G base r proper k ≠ 0) :=
  GeneratedDeckTransport.copiedRootReceipt G r.before.source.palette T.source.palette r.sourceRetained
    (oldTorsion G base r proper) T.ready.torsion r.currentGroup
    (input G base r proper).signature (input G base r proper).retained
    (input G base r proper).proper (r.batchLabels G base proper)
    (r.batchLabels_saved G base proper) k nonzero

/-- This is a branch address in the copied actual old card tree, including
repeated equal leaves. It never chooses an equal-valued palette row. -/
def cardLeaf (k : Key G base r proper) (nonzero : current G base r proper k ≠ 0)
    (p : Occurrences.Address (oldRoot G base r proper k nonzero).2) :
    CurrentOccurrences.Id G T.source.palette :=
  ⟨(copiedRoot G base r proper k nonzero).label,
    Occurrences.transportAddress (copiedRoot G base r proper k nonzero).saved.symm p⟩

theorem cardLeaf_saved (k : Key G base r proper) (nonzero : current G base r proper k ≠ 0)
    (p : Occurrences.Address (oldRoot G base r proper k nonzero).2) :
    CurrentOccurrences.savedLeaf G T.source.palette (cardLeaf G base r proper k nonzero p) =
      Occurrences.leaf (oldRoot G base r proper k nonzero).2 p :=
  Occurrences.transportAddress_leaf (copiedRoot G base r proper k nonzero).saved.symm p

theorem cardLeaf_injective (k : Key G base r proper) (nonzero : current G base r proper k ≠ 0) :
    Function.Injective (cardLeaf G base r proper k nonzero) := by
  intro p q he
  apply Occurrences.transportAddress_injective (copiedRoot G base r proper k nonzero).saved.symm
  exact @sigma_mk_injective (Fin T.source.palette.count)
    (fun i => Occurrences.Address (T.source.palette.trees i))
    (copiedRoot G base r proper k nonzero).label _ _ he

theorem cardLeaf_arity_le (k : Key G base r proper) (nonzero : current G base r proper k ≠ 0)
    (p : Occurrences.Address (oldRoot G base r proper k nonzero).2) :
    (CurrentOccurrences.savedLeaf G T.source.palette (cardLeaf G base r proper k nonzero p)).1.1 ≤
      (input G base r proper).m := by
  rw [cardLeaf_saved]
  exact (oldRoot G base r proper k nonzero).2.leaf_arity_le _
    (Occurrences.leaf_mem _ p)

theorem cardLeaf_arity_lt (k : Key G base r proper) (nonzero : current G base r proper k ≠ 0)
    (p : Occurrences.Address (oldRoot G base r proper k nonzero).2) :
    (CurrentOccurrences.savedLeaf G T.source.palette (cardLeaf G base r proper k nonzero p)).1.1 <
      (CurrentOccurrences.savedLeaf G T.source.palette o).1.1 := by
  have bound := cardLeaf_arity_le G base r proper k nonzero p
  have arity := congrArg Sigma.fst (r.selectedSignatureFinal G base proper)
  change (input G base r proper).m + 2 = _ at arity
  omega

/-- Genuine final no-unary/no-odd invariants leave binary or a smaller even
nonbinary prime. In particular, queue exhaustion does not make the latter empty. -/
theorem cardLeaf_cases (k : Key G base r proper) (nonzero : current G base r proper k ≠ 0)
    (p : Occurrences.Address (oldRoot G base r proper k nonzero).2) :
    (CurrentOccurrences.savedLeaf G T.source.palette (cardLeaf G base r proper k nonzero p)).1.1 = 2 ∨
      (4 ≤ (CurrentOccurrences.savedLeaf G T.source.palette (cardLeaf G base r proper k nonzero p)).1.1 ∧
       Even (CurrentOccurrences.savedLeaf G T.source.palette (cardLeaf G base r proper k nonzero p)).1.1) := by
  let q := cardLeaf G base r proper k nonzero p
  have positive := CurrentOccurrences.savedLeaf_positive G T.source.palette q
  have notUnary := CurrentFrontierClosure.no_current_unary G T.source.palette T.ready.noUnary q
  by_cases two : (CurrentOccurrences.savedLeaf G T.source.palette q).1.1 = 2
  · exact .inl two
  · have three : 3 ≤ (CurrentOccurrences.savedLeaf G T.source.palette q).1.1 := by omega
    have even := T.ready.noOdd _ (CurrentOccurrences.savedLeaf_retained G T.source.palette q)
      (CurrentOccurrences.savedLeaf_prime G T.source.palette q) three
    refine .inr ⟨?_,even⟩
    obtain ⟨n,hn⟩ := even
    change 4 ≤ (CurrentOccurrences.savedLeaf G T.source.palette q).1.1
    omega

/-- Precisely the missing implication: matching follows when the card's own
saved leaves are binary. Final minimum-core arguments establish this hypothesis
only when the selected occurrence is a final minimum. -/
theorem matching_of_binary_leaves (k : Key G base r proper)
    (nonzero : current G base r proper k ≠ 0)
    (binary : ∀ p : Occurrences.Address (oldRoot G base r proper k nonzero).2,
      (CurrentOccurrences.savedLeaf G T.source.palette (cardLeaf G base r proper k nonzero p)).1.1 = 2) :
    MatchingOrZero (actualTransfers T.source.palette.family) (current G base r proper k) := by
  have saved : ∀ f ∈ (oldRoot G base r proper k nonzero).2.leaves,
      f ∈ T.source.palette.family := by
    intro f member
    obtain ⟨p,hp⟩ := Occurrences.leaf_address_complete _ f member
    have retained := CurrentOccurrences.savedLeaf_retained G T.source.palette
      (cardLeaf G base r proper k nonzero p)
    rw [cardLeaf_saved, hp] at retained
    exact retained
  have allBinary : ∀ f ∈ (oldRoot G base r proper k nonzero).2.leaves, f.1 = 2 := by
    intro f member
    obtain ⟨p,hp⟩ := Occurrences.leaf_address_complete _ f member
    have two := binary p
    rw [cardLeaf_saved, hp] at two
    exact two
  have oldMatching := (oldRoot G base r proper k nonzero).2.matchingOrZero
    T.source.palette.family saved allBinary
  change MatchingOrZero (actualTransfers T.source.palette.family)
    (rawCard T.source.palette.family T.ready.torsion (input G base r proper).signature k)
  rw [(transport G base r proper k).equation]
  exact ContinuationTransport.matching_smul oldMatching _ (transport G base r proper k).nonzero

/-- Every failure of matching has an actual smaller even prime address in its
own copied card tree. This is stronger than existence of some equal family row. -/
theorem nonmatching_has_lower_leaf (k : Key G base r proper)
    (nonmatching : ¬ MatchingOrZero (actualTransfers T.source.palette.family)
      (current G base r proper k)) :
    ∃ nonzero : current G base r proper k ≠ 0,
      ∃ p : Occurrences.Address (oldRoot G base r proper k nonzero).2,
        4 ≤ (CurrentOccurrences.savedLeaf G T.source.palette
          (cardLeaf G base r proper k nonzero p)).1.1 ∧
        Even (CurrentOccurrences.savedLeaf G T.source.palette
          (cardLeaf G base r proper k nonzero p)).1.1 ∧
        (CurrentOccurrences.savedLeaf G T.source.palette
          (cardLeaf G base r proper k nonzero p)).1.1 <
          (CurrentOccurrences.savedLeaf G T.source.palette o).1.1 := by
  classical
  have nonzero : current G base r proper k ≠ 0 := fun hz => nonmatching (.inl hz)
  have notAll : ¬ ∀ p : Occurrences.Address (oldRoot G base r proper k nonzero).2,
      (CurrentOccurrences.savedLeaf G T.source.palette (cardLeaf G base r proper k nonzero p)).1.1 = 2 :=
    fun allBinary => nonmatching (matching_of_binary_leaves G base r proper k nonzero allBinary)
  push_neg at notAll
  obtain ⟨p,hp⟩ := notAll
  have lower := (cardLeaf_cases G base r proper k nonzero p).resolve_left hp
  exact ⟨nonzero,p,lower.1,lower.2,cardLeaf_arity_lt G base r proper k nonzero p⟩

/-- The raw card is physically available with both charged original-G
programmes, irrespective of which side of cardLeaf_cases is inhabited. -/
def cardAccess (k : Key G base r proper) :
    CurrentSignatureAccess G T.source.palette ⟨(input G base r proper).m,current G base r proper k⟩ :=
  r.currentRawAccess G base proper k

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentCoverage
end
