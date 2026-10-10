import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralCards
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralRankTwo
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralRankThree
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralRankFourCoverage
import Holant.Proofs.Dichotomy.Closure.External.GlobalCloseCompletionExternalTetrahedralCurrent

/-! The same prepared current prime q4 cannot have an actual I dictionary,
in either of its two physical placements. Rank exclusions and rank-four
coverage are the genuine full sixty-point coefficient theorems. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral
open Holant Holant.Tractable Holant.Algebraic Holant.Certificates
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient

 theorem prime_literal_deck_impossible (opposite : Bool) (q : FourTensor)
    (prime : Prime (⟨4,q⟩ : AnySignature ℂ)) (deck : Preserver.LiteralDeck opposite q) : False := by
  have twoSided := Preserver.two_sided opposite q deck
  have bound : (cardMatrix q).rank≤4 := by simpa using Matrix.rank_le_width (cardMatrix q)
  have h0 := Preserver.Completion.prime_rank_not_zero q prime
  have h1 := Preserver.Completion.prime_rank_not_one opposite q prime twoSided
  have h2 := RankTwo.no_rank_two opposite (cardMatrix q) twoSided
  have h3 := RankThree.no_rank_three opposite (cardMatrix q) twoSided
  have h4 := RankFour.prime_rank_not_four opposite q prime twoSided
  omega

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (same : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

include core same stable in
theorem literal_icosahedral_impossible (opposite : Bool)
    (literal : group (ClosureSourceRows.embedding G) P.family torsion=Dictionary.group opposite) : False := by
  have prime : Prime (⟨4,q⟩ : AnySignature (OI.K G)) := same ▸ core.prime
  let phi := complexEmbedding (ClosureSourceRows.embedding G)
  have hp : Prime (⟨4,RingHomRealization.mapSignature phi q⟩ : AnySignature ℂ) :=
    (prime_mapSignature_iff phi (⟨4,q⟩ : AnySignature (OI.K G))).mpr prime
  have deck : Preserver.LiteralDeck opposite (RingHomRealization.mapSignature phi q) :=
    Cards.current_literal_deck opposite G P torsion literal q core same stable
  exact prime_literal_deck_impossible opposite _ hp deck

include core same stable in
theorem semantic_icosahedral_impossible
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G) P.family torsion)
      (.platonic .icosahedral)) : False := by
  rcases Placement.current_two_displays (ClosureSourceRows.embedding G) P.family torsion
    P.equality semantic with literal | literal
  · exact literal_icosahedral_impossible G P torsion q core same stable false literal
  · exact literal_icosahedral_impossible G P torsion q core same stable true literal

namespace Q
export GeneratedGroupQ4Consumers (table minimum minimum_literal matching)
end Q
variable (base : Palette G)
variable {S T : GeneratedGroupWorklist.Active G base}
variable {trace : GeneratedGroupWorklist.Trace G base S T}
variable {o : CurrentOccurrences.Id G T.source.palette}
variable (receipt : GeneratedGroupWorklist.PreparationReceipt G base trace o)
variable (four : (CurrentOccurrences.savedLeaf G T.source.palette o).1.1=4)

include receipt four in
theorem prepared_semantic_icosahedral_impossible
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G)
      T.source.palette.family T.ready.torsion) (.platonic .icosahedral)) : False :=
  semantic_icosahedral_impossible G T.source.palette T.ready.torsion
    (Q.table G base four) (Q.minimum G base four) (Q.minimum_literal G base four)
    (Q.matching G base receipt four) semantic

/-- The only remaining semantic Platonic model at a prepared current q4
is O, and the actual current group is its full marked overgroup. -/
def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion) : Prop := match M with
  | .platonic p _ => p=.octahedral ∧
      group (ClosureSourceRows.embedding G) T.source.palette.family T.ready.torsion=
        overgroup (ClosureSourceRows.embedding G) T.source.palette.family T.ready.torsion
  | _ => True

include receipt four in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion) : ForMarking G base (T:=T) M := by
  cases M with
  | platonic p model =>
      constructor
      · cases p with
        | tetrahedral => exact (GlobalCloseCompletionTetrahedralCurrent.prepared_semantic_tetrahedral_impossible
            G base receipt four model).elim
        | octahedral => rfl
        | icosahedral => exact (prepared_semantic_icosahedral_impossible G base receipt four model).elim
      · exact GlobalCloseCompletionExternalTetrahedralCurrent.prepared_platonic_actual_eq_semantic
          G base receipt four p model
  | smallTwo => trivial
  | smallFour => trivial
  | cyclic => trivial
  | monomial => trivial
  | bilinear => trivial
  | unshifted => trivial
  | shifted => trivial

def ForResult (result : GeneratedGroupWorklist.Result G base) : Prop := match result with
  | .initialStop .. => True
  | .prepared _ _ (.inl _) => True
  | .prepared _ _ (.inr exhausted) =>
      ∀ (o : CurrentOccurrences.Id G exhausted.final.source.palette)
        (_four : (CurrentOccurrences.savedLeaf G exhausted.final.source.palette o).1.1=4),
        ForMarking G base (T:=exhausted.final)
          (ClosureMarkedActualReceipts.produce G exhausted.final.source.palette
            exhausted.final.ready.torsion).physical.marking

theorem forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := by
  cases result with
  | initialStop => trivial
  | prepared ready trace result =>
    cases result with
    | inl stop => trivial
    | inr exhausted =>
      intro o four
      exact forMarking G base (exhausted.preparationReceipt G base rfl o) four _

theorem original_current_platonic_q4_refinement : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral
end
