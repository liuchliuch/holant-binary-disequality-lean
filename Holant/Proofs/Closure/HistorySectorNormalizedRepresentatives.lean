import Holant.Proofs.Closure.HistorySectorCardsNetworks
import Holant.Proofs.Closure.ClosureSourceRowsMatching
import Holant.Marked.SupportAtlas.MarkedDeck

/-! Fixed actual phase representatives for the SAME constructed normalized
group. The actual key/table and a canonical pivot coefficient remain in the
original field; the separate coordinate multiplier remains algebraic. No
unit-normalized table or coordinate basis is installed as a source label. -/
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

structure PhaseIndex (p : Bool) (t : Phase N.m) where
  key : completeGroup P.family torsion
  multiplier : Scalar
  nonzero : multiplier ≠ 0
  transfer : sectorTransfer U ((actualRepresentative P.family torsion key).map (algebraicEmbedding G)) =
    scale multiplier (if p then S t.val else R t.val)

def phaseIndex (p : Bool) (t : Phase N.m) : PhaseIndex G P torsion U N p t := by
  let h := ClosureMarkedDihedralCoordinates.Source.source_sector_representative U
    (algebraicEmbedding G) P.family torsion N p t.val t.property
  let j := Classical.choose h
  let hj := Classical.choose_spec h
  let c := Classical.choose hj
  have hc := Classical.choose_spec hj
  exact ⟨j,c,hc.1,hc.2⟩

def originalCoefficient (p : Bool) (t : Phase N.m) : OI.K G :=
  let B := Holant.Projective.BoundedTorsion.binarySignature (actualRepresentative P.family torsion (phaseIndex G P torsion U N p t).key)
  B (firstWord B (actualRepresentative_signature_nonzero P.family torsion _))

theorem originalCoefficient_nonzero (p : Bool) (t : Phase N.m) :
    originalCoefficient G P torsion U N p t ≠ 0 :=
  firstWord_nonzero _ (actualRepresentative_signature_nonzero P.family torsion _)

/-- Original-field unit and normalized SOURCE table identity only. The
canonical table is not claimed actual or installed as a literal resource. -/
theorem originalCoefficient_equation (p : Bool) (t : Phase N.m) :
    Holant.Projective.BoundedTorsion.binarySignature (actualRepresentative P.family torsion (phaseIndex G P torsion U N p t).key) =
      fun x => originalCoefficient G P torsion U N p t * canonicalKey
        (Holant.Projective.BoundedTorsion.binarySignature (actualRepresentative P.family torsion (phaseIndex G P torsion U N p t).key)) x :=
  recover_from_key _ (actualRepresentative_signature_nonzero P.family torsion _)

def coordinateMultiplier (p : Bool) (t : Phase N.m) : Scalar :=
  (phaseIndex G P torsion U N p t).multiplier /
    algebraicEmbedding G (originalCoefficient G P torsion U N p t)

theorem coordinateMultiplier_nonzero (p : Bool) (t : Phase N.m) :
    coordinateMultiplier G P torsion U N p t ≠ 0 :=
  div_ne_zero (phaseIndex G P torsion U N p t).nonzero
    ((map_ne_zero (algebraicEmbedding G)).mpr (originalCoefficient_nonzero G P torsion U N p t))

theorem multiplier_original_split (p : Bool) (t : Phase N.m) :
    (phaseIndex G P torsion U N p t).multiplier =
      algebraicEmbedding G (originalCoefficient G P torsion U N p t) *
        coordinateMultiplier G P torsion U N p t := by
  unfold coordinateMultiplier
  have hc := (map_ne_zero (algebraicEmbedding G)).mpr
    (originalCoefficient_nonzero G P torsion U N p t)
  rw [div_eq_mul_inv,mul_left_comm _ (phaseIndex G P torsion U N p t).multiplier,
    mul_inv_cancel₀ hc,mul_one]

def representatives : Representatives (ClosureSourceRows.ambientFamily G P) N.m U where
  matrix p t := ClosureSourceRows.representative G P torsion (phaseIndex G P torsion U N p t).key
  multiplier p t := (phaseIndex G P torsion U N p t).multiplier
  multiplier_ne_zero p t := (phaseIndex G P torsion U N p t).nonzero
  actual p t := ClosureSourceRows.representative_actual G P torsion (phaseIndex G P torsion U N p t).key
  transfer p t := (phaseIndex G P torsion U N p t).transfer

/-- The actual ORIGINAL-field binary, with both charged original-G programmes.
The coordinate multiplier is not applied to this source table. -/
def representativeAccess (p : Bool) (t : Phase N.m) :
    CurrentSignatureAccess G P ⟨2,Holant.Projective.BoundedTorsion.binarySignature
      (actualRepresentative P.family torsion (phaseIndex G P torsion U N p t).key)⟩ :=
  ClosureSourceRows.representativeAccess G P torsion (phaseIndex G P torsion U N p t).key

variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (hcore : core.signature = ⟨4,q⟩)
variable (stable : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)
include core hcore stable

/-- This q4 condition is DERIVED from the SAME CURRENT raw deck. The closing
representatives come from the SAME actual source keys and normalized group. -/
theorem physicalDeck : ∀ (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase N.m),
    physicalCard (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q) e
      ((representatives G P torsion U N).matrix p t) = 0 ∨
    sectorTransfer U (physicalCard
      (Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature (algebraicEmbedding G) q) e
      ((representatives G P torsion U N).matrix p t)) ∈ groupM N.m := by
  intro e p t
  let j := (phaseIndex G P torsion U N p t).key
  let B := actualRepresentative P.family torsion j
  rcases ClosureSourceRows.actualCard_actual_or_zero G P torsion q stable core hcore e B
    (actualRepresentative_actual P.family torsion j) with hz | actual
  · left
    change physicalCard _ e (B.map (algebraicEmbedding G)) = 0
    rw [ClosureSourceRows.sourceCard_actual,hz]
    funext a b
    simp [binaryMatrix,Matrix.map_apply]
  · right
    change sectorTransfer U (physicalCard _ e (B.map (algebraicEmbedding G))) ∈ groupM N.m
    rw [ClosureSourceRows.sourceCard_actual]
    exact ClosureMarkedDihedralCoordinates.Source.actual_sector_spectrum U
      (algebraicEmbedding G) P.family torsion N
      (binaryMatrix (ClosureSourceRows.originalOrderedCard q e B)) actual

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorNormalized
end
