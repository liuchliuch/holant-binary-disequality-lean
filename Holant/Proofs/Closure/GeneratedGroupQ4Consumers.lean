import Holant.Proofs.Closure.GroupPreparedStability
import Holant.Proofs.Closure.FrontierQ4
import Holant.Proofs.Closure.ClosureSourceRowsC2Physical
import Holant.Proofs.Closure.ClosureSourceRowsMonomialPhysical
import Holant.Proofs.Closure.ClosureSourceRowsKleinNative
import Holant.Proofs.Closure.HistorySectorNormalizedMarking

/-! Concrete q4 consumers for EACH addressed occurrence of an actually exhausted
current-group preparation. Its OWN recorded event proves the current raw deck;
no value-level reselection of an equal prime replaces the supplied occurrence.
C2/native-M/Klein guards and physical endpoints, and the same-marking q4 B/A
weighted root decks, are produced internally. Other sectors
remain explicit. Higher-arity local classification is not asserted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupQ4Consumers
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {S T : GeneratedGroupWorklist.Active G base}
variable {h : GeneratedGroupWorklist.Trace G base S T}
variable {q : CurrentOccurrences.Id G T.source.palette}
variable (r : GeneratedGroupWorklist.PreparationReceipt G base h q)
variable (four : (CurrentOccurrences.savedLeaf G T.source.palette q).1.1 = 4)

def table : Signature (OI.K G) 4 :=
  FrontierQ4.tableFour (CurrentOccurrences.savedLeaf G T.source.palette q).1 four

def minimum : MinimumCore T.source.palette.family :=
  FrontierQ4.minimumOfFour T.source.palette.family
    (CurrentOccurrences.savedLeaf G T.source.palette q).1
    (CurrentOccurrences.savedLeaf_retained G T.source.palette q)
    (CurrentOccurrences.savedLeaf_prime G T.source.palette q) four T.ready.noOdd

theorem minimum_literal : (minimum G base four).signature = ⟨4,table G base four⟩ :=
  (FrontierQ4.tableFour_exact (CurrentOccurrences.savedLeaf G T.source.palette q).1 four).symm

/-- The prepared deck is derived from this q's exact trace receipt. -/
def prepared : GroupPreparedStability.PreparedDeck G T.source.palette
    T.ready.torsion (minimum G base four) :=
  GroupPreparedStability.fromReceipt G base r (minimum G base four) rfl

include r in
/-- CURRENT raw matching for the exact supplied q4 table follows from the
actual recorded preparation, final no-unary and same final-group receipts. -/
theorem matching : ∀ g ∈ rawDeck T.source.palette.family T.ready.torsion
    (table G base four), MatchingOrZero (actualTransfers T.source.palette.family) g := by
  rcases prepared G base r four with ⟨m,f,proper,even,literal,stable⟩
  have hsig := literal.symm.trans (minimum_literal G base four)
  have hm : m = 2 := by
    have hn := congrArg Sigma.fst hsig
    change m+2 = 4 at hn
    omega
  subst m
  have hf : f = table G base four := sigma_mk_injective hsig
  subst f
  exact stable

/-- All successful endpoints carry their actual original-G programmes;
failed concrete guards retain their actual alternate-sector evidence. -/
structure Receipt : Type 1 where
  c2 : ClosureSourceRows.C2Attempt G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
  nativeM : ClosureSourceRows.NativeMAttempt G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four)
  klein : ClosureSourceRows.KleinAttempt G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four)
  nativeKlein : ClosureSourceRows.NativeKleinAttempt G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four)
  normalized : HistorySectorNormalized.Result G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four)

def produce : Receipt G base r four :=
  ⟨ClosureSourceRows.attemptC2 G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four),
   ClosureSourceRows.attemptNativeM G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four),
   ClosureSourceRows.attemptKlein G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four),
   ClosureSourceRows.attemptNativeKlein G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four),
   HistorySectorNormalized.produce G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four)⟩

/-- Every addressed q4 uses the SAME final palette marking; its own event and
raw deck determine the card receipt, not a new basis choice for that value. -/
theorem normalized_same_marking : (produce G base r four).normalized.cards.marking =
    ClosureMarkedActualReceipts.produce G T.source.palette T.ready.torsion :=
  HistorySectorNormalized.same_marking G T.source.palette T.ready.torsion
    (table G base four) (minimum G base four) (minimum_literal G base four)
    (matching G base r four)

/-- No preparation receipt is an extra input to this exhausted-run factory. -/
def forExhausted {A : GeneratedGroupWorklist.Active G base}
    (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done = ∅)
    (q : CurrentOccurrences.Id G R.final.source.palette)
    (four : (CurrentOccurrences.savedLeaf G R.final.source.palette q).1.1 = 4) :
    Receipt G base (R.preparationReceipt G base noPrior q) four :=
  produce G base (R.preparationReceipt G base noPrior q) four

/-- Structural stops need no invented q4 classification. In the exhausted
case EVERY addressed final q4 occurrence is covered, including duplicates. -/
def ForResult (R : GeneratedGroupWorklist.Result G base) : Type 1 := match R with
  | .initialStop _ _ => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ∀ (q : CurrentOccurrences.Id G exhausted.final.source.palette)
        (four : (CurrentOccurrences.savedLeaf G exhausted.final.source.palette q).1.1 = 4),
        Receipt G base (exhausted.preparationReceipt G base rfl q) four

def forResult (R : GeneratedGroupWorklist.Result G base) : ForResult G base R := match R with
  | .initialStop _ _ => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) => fun q four => forExhausted G base exhausted rfl q four

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedGroupQ4Consumers
end
