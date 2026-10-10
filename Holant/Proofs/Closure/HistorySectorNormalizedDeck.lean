import Holant.Proofs.Closure.HistorySectorNormalizedRepresentatives

/-! Concrete q4 weighted-root-card hypotheses for a SAME constructed B/A
sector. The physical deck and its weighted normal form are conclusions of
CURRENT original-deck stability, not supplied sector-deck assumptions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) (sameBasis : params.basis = U)
include sameBasis
variable (q : Signature (OI.K G) 4)

def markedRepresentatives : Representatives (ClosureSourceRows.ambientFamily G P) N.m params.basis where
  matrix := (representatives G P torsion U N).matrix
  multiplier := (representatives G P torsion U N).multiplier
  multiplier_ne_zero := (representatives G P torsion U N).multiplier_ne_zero
  actual := (representatives G P torsion U N).actual
  transfer p t := by
    rw [sameBasis]
    exact (representatives G P torsion U N).transfer p t

theorem markedPhysicalDeck (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    PhysicalDeck (ClosureSourceRows.ambientFamily G P) params
      (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q)
      (markedRepresentatives G P torsion U N params sameBasis) := by
  intro e p t
  change physicalCard _ e ((representatives G P torsion U N).matrix p t) = 0 ∨
    sectorTransfer params.basis (physicalCard _ e ((representatives G P torsion U N).matrix p t)) ∈ groupM N.m
  rw [sameBasis]
  exact physicalDeck G P torsion U N q core hcore stable e p t

theorem safeWeightedDeck (nonstandard : nonstandard params)
    (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    SafeDeck N.m (delta params : ℂ)
      (complexTensor (U.symm.action
        (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q))) := by
  have h := safeDeck_of_physical (ClosureSourceRows.ambientFamily G P) params nonstandard
    (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q)
    (markedRepresentatives G P torsion U N params sameBasis)
    (markedPhysicalDeck G P torsion U N params sameBasis q core hcore stable)
  simpa only [sameBasis] using h

/-- The literal edge scalar is retained alongside the normalized edge. -/
theorem normalized_edge : sectorEdge U = scale params.edgeMultiplier params.edgeNormal := by
  simpa only [sameBasis] using params.edge_exact

theorem normalized_card (nonstandard : nonstandard params)
    (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase N.m) :
    transport U (physicalCard
      (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q) e
      ((markedRepresentatives G P torsion U N params sameBasis).matrix p t)) =
      scale (params.edgeMultiplier *
        (markedRepresentatives G P torsion U N params sameBasis).multiplier p t)
        (contract0 (reorder (U.symm.action
          (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q)) e)
          (Kernel.mul (diagonalKernel 1 (delta params)) (if p then S t.val else R t.val))) := by
  have h := physical_card_normalization (ClosureSourceRows.ambientFamily G P) params nonstandard
    (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q)
    (markedRepresentatives G P torsion U N params sameBasis) e p t
  simpa only [sameBasis] using h

structure RootDeck : Type 1 where
  physical : PhysicalDeck (ClosureSourceRows.ambientFamily G P) params
    (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q)
    (markedRepresentatives G P torsion U N params sameBasis)
  normalized : SafeDeck N.m (delta params : ℂ)
    (complexTensor (U.symm.action
      (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q)))
  edge : sectorEdge U = scale params.edgeMultiplier params.edgeNormal
  phaseAccess : ∀ p t, CurrentSignatureAccess G P ⟨2,Holant.Projective.BoundedTorsion.binarySignature
    (actualRepresentative P.family torsion (phaseIndex G P torsion U N p t).key)⟩

def rootDeck (nonstandard : nonstandard params) (core : MinimumCore P.family)
    (hcore : core.signature = ⟨4,q⟩)
    (stable : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g) :
    RootDeck G P torsion U N params sameBasis q where
  physical := markedPhysicalDeck G P torsion U N params sameBasis q core hcore stable
  normalized := safeWeightedDeck G P torsion U N params sameBasis q nonstandard core hcore stable
  edge := normalized_edge G P torsion U N params sameBasis
  phaseAccess := representativeAccess G P torsion U N

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
end
