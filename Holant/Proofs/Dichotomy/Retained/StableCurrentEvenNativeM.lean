import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenSupport
import Holant.Proofs.Dichotomy.Retained.StableCurrentBinaryClosure
import Holant.Proofs.Closure.GeneratedGroupQ4Consumers
import Holant.Proofs.Closure.ClosureNativeMCore

/-! A genuine higher-even product-membership branch at the engine's native-M
marking. The exact prepared raw deck proves complementary support. The small
support branch then has an explicit product formula. Every q4 occurrence uses
its own recorded preparation, while every unary/binary and the native edge use
the same marked basis. Larger support and the other markings remain explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenNativeM
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation CurrentFrontierClosure
open Holant.Certificates.EqualityQuaternary Holant.Marked.SupportAtlas

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

/-- A numerical condition on the actual stored table, independently decidable
from the desired tractable-class conclusion. -/
def TwoPointFour (f : AnySignature (OI.K G)) : Prop :=
  ∃ arity : f.1 = 4,
    ((Finset.univ : Finset (Fin 4 → Bool)).filter
      fun x => FrontierQ4.tableFour f arity x ≠ 0).card ≤ 2

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature = ⟨4,q⟩)
variable (stable : ∀ g ∈ rawDeck P.family torsion q,
  MatchingOrZero (actualTransfers P.family) g)

include P torsion N core literal stable

/-- The complete retained row and all physical source cards are constructed
from the actual raw-deck invariant, with no support hypothesis. -/
theorem current_complement_closed :
    ∀ x, q (complementWord x) = 0 ↔ q x = 0 := by
  let embedded := Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature
    (ClosureSourceRows.embedding G) q
  let reps := ClosureSourceRows.monomialRepresentatives G P torsion N q core literal
  have physical := ClosureSourceRows.monomial_sourceDeck G P torsion N q core literal stable
  have deck := deckSupport_of_samples N.range 1 one_ne_zero (by simp)
    (complexTensor embedded) (monomial_safeDeck N.range reps embedded physical)
  intro x
  have h : nonzeroBit (complexTensor embedded (Holant.Marked.SupportAtlas.complement x)) = false ↔
      nonzeroBit (complexTensor embedded x) = false := by rw [complement_eq deck x]
  have left : nonzeroBit (complexTensor embedded (Holant.Marked.SupportAtlas.complement x)) = false ↔
      q (complementWord x) = 0 := by
    change nonzeroBit (complexTensor embedded (complementWord x)) = false ↔ _
    simp [embedded,complexTensor,Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature]
  have right : nonzeroBit (complexTensor embedded x) = false ↔ q x = 0 := by
    simp [embedded,complexTensor,Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature]
  exact left.symm.trans (h.trans right)

/-- This closes a quaternary leaf at the actual native-M basis. The support
condition is tested on its original source-field coefficients. -/
theorem current_four_product_of_small
    (small : ((Finset.univ : Finset (Fin 4 → Bool)).filter fun x => q x ≠ 0).card ≤ 2) :
    leafPredicate G productClass InvertibleKernel.identity
      (⟨4,q⟩ : AnySignature (OI.K G)) := by
  let embedded := Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature
    (ClosureSourceRows.embedding G) q
  have closed : ∀ x, embedded (complementWord x) = 0 ↔ embedded x = 0 := by
    intro x
    simpa [embedded,Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature] using
      current_complement_closed G P torsion N q core literal stable x
  have hsmall : ((Finset.univ : Finset (Fin 4 → Bool)).filter fun x => embedded x ≠ 0).card ≤ 2 := by
    simpa [embedded,Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature] using small
  have product := StableCurrentEvenSupport.product_of_complement_closed_small embedded 0 closed hsmall
  change Product (InvertibleKernel.identity.symm.action embedded)
  simpa using product

/-- Closed alternative for the actual table. A larger support is kept as the
mathematical residual domain, rather than called a hardness result. -/
theorem current_four_product_or_large_support :
    leafPredicate G productClass InvertibleKernel.identity
      (⟨4,q⟩ : AnySignature (OI.K G)) ∨
    3 ≤ ((Finset.univ : Finset (Fin 4 → Bool)).filter fun x => q x ≠ 0).card := by
  classical
  by_cases small : ((Finset.univ : Finset (Fin 4 → Bool)).filter fun x => q x ≠ 0).card ≤ 2
  · exact Or.inl (current_four_product_of_small G P torsion N q core literal stable small)
  · exact Or.inr (by omega)

omit P torsion N core literal stable

section PreparedCurrent
variable (base : Palette G)
variable {S T : GeneratedGroupWorklist.Active G base}
variable {h : GeneratedGroupWorklist.Trace G base S T}
variable {o : CurrentOccurrences.Id G T.source.palette}
variable (r : GeneratedGroupWorklist.PreparationReceipt G base h o)
variable (NM : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    T.source.palette.family T.ready.torsion))

include r NM in
/-- This exact occurrence's recorded event supplies the complete current
deck. No regenerated matching or local membership is an input to the theorem. -/
theorem prepared_current_product
    (small : TwoPointFour G (CurrentOccurrences.savedLeaf G T.source.palette o).1) :
    leafPredicate G productClass InvertibleKernel.identity
      (CurrentOccurrences.savedLeaf G T.source.palette o).1 := by
  obtain ⟨four,small⟩ := small
  have result := current_four_product_of_small G T.source.palette T.ready.torsion NM
    (GeneratedGroupQ4Consumers.table G base four)
    (GeneratedGroupQ4Consumers.minimum G base four)
    (GeneratedGroupQ4Consumers.minimum_literal G base four)
    (GeneratedGroupQ4Consumers.matching G base r four) small
  change leafPredicate G productClass InvertibleKernel.identity
    (⟨4,FrontierQ4.tableFour (CurrentOccurrences.savedLeaf G T.source.palette o).1 four⟩ :
      AnySignature (OI.K G)) at result
  rwa [FrontierQ4.tableFour_exact] at result
end PreparedCurrent

/-- A real current subfamily that includes higher-even saved leaves. Distinct
stored occurrences are visited independently before values enter this set. -/
def resolvedFamily (P : Palette G) : SignatureFamily AlgebraicComplex :=
  Set.range (fun o : {o : CurrentOccurrences.Id G P //
      (CurrentOccurrences.savedLeaf G P o).1.1 ≤ 2 ∨
      TwoPointFour G (CurrentOccurrences.savedLeaf G P o).1} =>
    embed G (CurrentOccurrences.savedLeaf G P o.val).1)

variable (base : Palette G) {S : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base S) (noPrior : S.source.done = ∅)
variable (NM : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    R.final.source.palette.family R.final.ready.torsion))

include noPrior NM in
/-- The full exhausted trace supplies every addressed preparation internally.
The shared edge and every binary use this very same identity marking. -/
theorem exhausted_same_basis :
    IsCommonKBasis productClass (resolvedFamily G R.final.source.palette)
      InvertibleKernel.identity := by
  let P := R.final.source.palette
  let tau := R.final.ready.torsion
  let M : ClosureMarkedSourceRouting.Marking (StableCurrentBinaryClosure.embedding G) P.family tau :=
    .monomial NM
  have small := StableCurrentBinaryClosure.small_current_products G P tau M
    InvertibleKernel.identity rfl
  refine ⟨small.edge,?_⟩
  rintro _ ⟨⟨o,domain⟩,rfl⟩
  rcases domain with binary | four
  · exact small.leaves o binary
  · exact prepared_current_product G base (R.preparationReceipt G base noPrior o) NM four

include noPrior NM in
theorem exhausted_common_presentation :
    CommonKPresentationInKCoordinates productClass (resolvedFamily G R.final.source.palette) :=
  ⟨Set.finite_range _,InvertibleKernel.identity,exhausted_same_basis G base R noPrior NM⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableCurrentEvenNativeM
end
