import Holant.Proofs.Closure.ClosureCyclicCurrentPhase
import Holant.Proofs.Closure.ClosureSourceRowsC2Deck
import Holant.Proofs.Algorithms.CyclicBoundary.AlgebraicSource

/-! CURRENT q4 raw stability supplies the real cyclic PhysicalCards for the
internally selected original phase representatives. All deleted pairs and both
residual orders are literal raw keys of this q and this current family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (τ : ResidualTorsion P.family)
variable (N : C.NativeCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
variable (q : Signature (OI.K G) 4)
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
variable (stable : ∀ g ∈ rawDeck P.family τ q, MatchingOrZero (actualTransfers P.family) g)

include core hcore stable in
/-- Zero cards stay zero; each nonzero card is an actual source binary and
inherits its original-field cyclic ratio, rather than an assumed safe model. -/
theorem physicalCards : Physical.PhysicalCards
    (representatives (ClosureSourceRows.embedding G) P.family τ N)
    (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q) := by
  intro i side order t
  let B := actualRepresentative P.family τ
    (phaseIndex (ClosureSourceRows.embedding G) P.family τ N t).key
  have hB := actualRepresentative_actual P.family τ
    (phaseIndex (ClosureSourceRows.embedding G) P.family τ N t).key
  let e := ClosureSourceRows.pairPermutation i side order
  have card : Holant.Projective.CyclicQuaternary.Physical.orderedPhysicalCard
      (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q) i side order (B.map (ClosureSourceRows.embedding G)) =
      (binaryMatrix (ClosureSourceRows.originalOrderedCard q e B)).map (ClosureSourceRows.embedding G) := by
    rw [← ClosureSourceRows.pairPermutation_card]
    exact ClosureSourceRows.sourceCard_actual G q e B
  have transferCard : Physical.physicalTransfer
      (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q) i side order
      ((representatives (ClosureSourceRows.embedding G) P.family τ N).matrix t) =
      Kernel.mul (Physical.walshBinary
        ((binaryMatrix (ClosureSourceRows.originalOrderedCard q e B)).map (ClosureSourceRows.embedding G))) CP.Z := by
    change Kernel.mul (Physical.walshBinary
      (Holant.Projective.CyclicQuaternary.Physical.orderedPhysicalCard
        (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q) i side order
        (B.map (ClosureSourceRows.embedding G)))) CP.Z = _
    rw [card]
  rw [transferCard]
  rcases ClosureSourceRows.actualCard_actual_or_zero G P τ q stable core hcore e B hB with hz | ha
  · left
    rw [hz]
    funext a b
    simp [binaryMatrix,Matrix.map_apply,Physical.walshBinary,Kernel.mul,Kernel.transpose]
  · right
    exact actual_physical_phase (ClosureSourceRows.embedding G) P.family τ N _ ha

/-- The exact Hadamard edge and original-field phase pivot are exported
alongside the source card condition. -/
theorem same_edge : sectorEdge C.basis = scale 2 (diagonalKernel 1 (-1)) :=
  ClosureMarkedCyclic.same_edge

def selected (cyclic : IsCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
    (range : 3 ≤ Nat.card (D.group (ClosureSourceRows.embedding G) P.family τ)) :=
  ClosureMarkedCyclic.Source.nativeCyclic (ClosureSourceRows.embedding G) P.family τ P.equality cyclic range

theorem selected_even
    (cyclic : IsCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
    (range : 3 ≤ Nat.card (D.group (ClosureSourceRows.embedding G) P.family τ)) :
    Even (selected G P τ cyclic range).m := by
  letI := ClosureFieldBridgeGroups.actualFiniteGroup
    (D.complexEmbedding (ClosureSourceRows.embedding G)) P.family τ
  rw [← (selected G P τ cyclic range).cardinal]
  exact ClosureMarkedCyclic.native_order_even _
    (ClosureMarkedDihedral.Source.nativeX_mem (ClosureSourceRows.embedding G) P.family τ P.equality)

include q core hcore stable in
/-- Closed actual cyclic q4 source dispatch. Representatives and PhysicalCards
are internally constructed from CURRENT resources and THIS q's stable raw deck.
All endpoint/outside/doubled alternatives are kept literally. -/
theorem source_dispatch
    (cyclic : IsCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
    (range : 3 ≤ Nat.card (D.group (ClosureSourceRows.embedding G) P.family τ)) :
    CyclicBoundary.SourceDispatch.EndpointOutput
      (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) ∨
    Nonempty (CyclicBoundary.ActualCards.OutsideCard
      (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family)
      (selected G P τ cyclic range).m) ∨
    Nonempty (CyclicBoundary.NonsquareExit.DoubledOutside
      (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family)
      (selected G P τ cyclic range).m) := by
  let N := selected G P τ cyclic range
  have retained : (⟨4,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q⟩ : AnySignature AlgebraicComplex) ∈
      RingHomRealization.mapFamily (ClosureSourceRows.embedding G) P.family :=
    ⟨⟨4,q⟩,by simpa only [hcore] using core.retained,rfl⟩
  have prime : Prime (⟨4,RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q⟩ : AnySignature AlgebraicComplex) := by
    apply (prime_mapSignature_iff (ClosureSourceRows.embedding G) (⟨4,q⟩ : AnySignature (OI.K G))).mpr
    simpa only [hcore] using core.prime
  have output := CyclicBoundary.AlgebraicSource.source_order_at_least_four
    (representatives (ClosureSourceRows.embedding G) P.family τ N) N.range
    (selected_even G P τ cyclic range) _ retained prime
    (physicalCards G P τ N q core hcore stable)
  have family : RingHomRealization.mapFamily CyclicBoundary.AlgebraicRepresentatives.inclusion
      (RingHomRealization.mapFamily (ClosureSourceRows.embedding G) P.family) =
      RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family := by
    ext f
    constructor
    · rintro ⟨u,⟨v,hv,rfl⟩,rfl⟩
      exact ⟨v,hv,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨Holant.LocalDrafts.FinitePGL2.Stabilization.mapSignature (ClosureSourceRows.embedding G) v,
        ⟨v,hv,rfl⟩,rfl⟩
  rwa [family] at output

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
