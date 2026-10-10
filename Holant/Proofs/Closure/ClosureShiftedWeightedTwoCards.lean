import Holant.Proofs.Closure.ClosureShiftedWeightedPrimeAnchor

/-! Actual CURRENT two-card localization covariance at the saved source
anchor. The outside pair uses its literal matching endpoints, its common gauge
and an internally selected original-field connection key. Zero cards are
allowed, and no successful factor-line or compiler is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
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
variable (params : Parameters N.m) {k : ℕ} (f : Signature (OI.K G) (k+4))
variable (order : Equiv.Perm (Fin (k+4)))
variable (A : SourceAnchor G P torsion U N params f order)

def anchorCut (e d : Fin A.native.edges) : Equiv.Perm (Fin (k+2)) :=
  let M := HistorySectorCards.matching (algebraicEmbedding G) U A.native
  ClosureStableFactor.pairOrder (M.ports (e,true)) (M.ports (d,false))

def anchoredOutside (p₀ : Bool) (t₀ : Phase N.m) (e d : Fin A.native.edges)
    (p : Bool) (t : Phase N.m) : Signature (OI.K G) k :=
  outsideSource G P torsion U N params (SourceCard G P torsion U N f order p₀ t₀)
    (anchorCut G P torsion U N params f order A e d) p true t

variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
include sameBasis nonstandard
/-- Same saved source anchor, literal ports and actual current ancestor.
Both connection and normalization scalars retain their existing key identity. -/
theorem anchored_current_two_card (p₀ : Bool) (t₀ : Phase N.m) (e d : Fin A.native.edges)
    (p : Bool) (t : Phase N.m) :
    Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
      (Tensor.reindex (anchorCut G P torsion U N params f order A e d).symm
        (WeightedGauge.gauge (anchorWeights G P torsion U N params f order A)
          (U.symm.action (RH.mapSignature (algebraicEmbedding G)
            (SourceCard G P torsion U N f order p₀ t₀))))) =
      connectionScalar G P torsion U N params p true t •
        WeightedGauge.gauge (fun j => anchorWeights G P torsion U N params f order A
          ((anchorCut G P torsion U N params f order A e d) j.succ.succ))
          (U.symm.action (RH.mapSignature (algebraicEmbedding G)
            (anchoredOutside G P torsion U N params f order A p₀ t₀ e d p t))) := by
  have weights := matching_cross_weights
    (HistorySectorCards.matching (algebraicEmbedding G) U A.native) (delta params) e d
  exact balanced_pair_covariance G P torsion U N params
    (SourceCard G P torsion U N f order p₀ t₀)
    (anchorCut G P torsion U N params f order A e d) sameBasis nonstandard
    (anchorWeights G P torsion U N params f order A) p true t weights.1 weights.2

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
