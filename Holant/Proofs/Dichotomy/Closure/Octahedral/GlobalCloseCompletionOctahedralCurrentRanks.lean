import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCards
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralSplit

/-! Actual-current octahedral rank restrictions on the unchanged minimum
q4. The rank-four contradiction reconstructs factors on those same ports. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralCurrentRanks
open Holant Holant.Algebraic Holant.Tractable
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (same : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)
abbrev embedded : FourTensor :=
  RingHomRealization.mapSignature (complexEmbedding (ClosureSourceRows.embedding G)) q

def Output : Prop := ∃ f : Form,
  group (ClosureSourceRows.embedding G) P.family torsion=Coordinates.Models.group f ∧
  Preserver.LiteralDeck f (embedded G q) ∧
  ∀ e : Preserver.PortOrder,
    TwoSided (Preserver.Roots f) (Preserver.transferMatrix (embedded G q) e) ∧
    ((Preserver.transferMatrix (embedded G q) e).rank=2 ∨
      (Preserver.transferMatrix (embedded G q) e).rank=3)

include core same stable in
theorem produce
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G) P.family torsion)
      (.platonic .octahedral)) : Output G P torsion q := by
  have prime : Prime (⟨4,q⟩ : AnySignature (OI.K G)) := same ▸ core.prime
  have hp := PrimalityInterfaces.embedded_prime
    (complexEmbedding (ClosureSourceRows.embedding G)) q prime
  obtain ⟨f,hf,deck⟩ := GlobalCloseCompletionOctahedralCards.actual_marked_deck
    G P torsion q core same stable semantic
  refine ⟨f,hf,deck,?_⟩
  intro e
  have twoSided := (Preserver.deck_iff_transfer_all_orders f (embedded G q)).mp deck e
  have noFour := RankFour.ExactAutomorphisms.original_prime_no_rankFour
    (complexEmbedding (ClosureSourceRows.embedding G)) q prime f e twoSided.1
  have ranks := Preserver.prime_possible_ranks (embedded G q) hp.1 hp.2 e
  exact ⟨twoSided,ranks.elim Or.inl (fun h=>Or.inr (h.resolve_right noFour))⟩

variable (base : Palette G)
variable {S T : GeneratedGroupWorklist.Active G base}
variable {trace : GeneratedGroupWorklist.Trace G base S T}
variable {o : CurrentOccurrences.Id G T.source.palette}
variable (receipt : GeneratedGroupWorklist.PreparationReceipt G base trace o)
variable (four : (CurrentOccurrences.savedLeaf G T.source.palette o).1.1=4)

include receipt four in
theorem prepared
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      T.source.palette.family T.ready.torsion) (.platonic .octahedral)) :
    Output G T.source.palette T.ready.torsion (Q.table G base four) :=
  produce G T.source.palette T.ready.torsion
    (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
    (Q.matching G base receipt four) semantic


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralCurrentRanks
end
