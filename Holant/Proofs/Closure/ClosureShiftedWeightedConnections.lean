import Holant.Proofs.Closure.ClosureShiftedWeightedPencil

/-! Exact actual-key connections for coherent weighted localization. A pair
with one unit gauge weight and one delta weight has internally selected
original-source phase preimages, including both endpoint orientations. The
coordinate normalization scalar is separate from the literal original-field
binary and its charged original-G access. -/
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
variable (params : Parameters N.m)

/-- orientation=true places delta at the first endpoint, false at the second. -/
def balancedPhase (p orientation : Bool) (t : Phase N.m) : Phase N.m :=
  ⟨if p then (if orientation then t.val⁻¹ else (delta params)^2/t.val) else t.val,by
    cases p
    · exact t.property
    · cases orientation
      · exact (delta_root params).div t.property
      · exact t.property.inv⟩

def balancedScalar (p orientation : Bool) (t : Phase N.m) : Scalar :=
  if p then (if orientation then t.val else t.val/delta params) else 1

theorem balancedScalar_nonzero (p orientation : Bool) (t : Phase N.m) :
    balancedScalar G P torsion U N params p orientation t ≠ 0 := by
  have ht := t.property.ne_zero (by have := N.range; omega)
  cases p <;> cases orientation <;> simp [balancedScalar,ht,delta_ne_zero params]

/-- Exact two-endpoint port-gauge push. The squared-phase shift is a real root. -/
theorem balanced_kernel (p orientation : Bool) (t : Phase N.m) :
    Kernel.mul
      (Kernel.mul (WeightedGauge.diagonal (if orientation then delta params else 1))
        (Holant.Dihedral.CompatibleClosure.M p t.val))
      (WeightedGauge.diagonal (if orientation then 1 else delta params)) =
    scale (balancedScalar G P torsion U N params p orientation t)
      (Kernel.mul (D (delta params))
        (if p then S (balancedPhase G P torsion U N params p orientation t).val
          else R (balancedPhase G P torsion U N params p orientation t).val)) := by
  have ht := t.property.ne_zero (by have := N.range; omega)
  have hd := delta_ne_zero params
  funext a b
  cases p <;> cases orientation <;> cases a <;> cases b <;>
    simp [WeightedGauge.diagonal,WeightedGauge.bitWeight,D,diagonalKernel,
      Holant.Dihedral.CompatibleClosure.M,Holant.Marked.monomial,R,S,
      Signature.disequality,Kernel.mul_apply,scale,balancedPhase,balancedScalar] <;>
    field_simp [ht,hd] <;> ring

def connectionKey (p orientation : Bool) (t : Phase N.m) : completeGroup P.family torsion :=
  (HistorySectorNormalized.phaseIndex G P torsion U N p
    (balancedPhase G P torsion U N params p orientation t)).key

def sourceConnection (p orientation : Bool) (t : Phase N.m) : Mat :=
  Kernel.pullback (HistorySectorCards.mapBinary (algebraicEmbedding G)
    (X * actualRepresentative P.family torsion (connectionKey G P torsion U N params p orientation t) * X)) U.matrix

def connectionScalar (p orientation : Bool) (t : Phase N.m) : Scalar :=
  balancedScalar G P torsion U N params p orientation t /
    phaseScalar G P torsion U N params p (balancedPhase G P torsion U N params p orientation t)

theorem connectionScalar_nonzero (p orientation : Bool) (t : Phase N.m) :
    connectionScalar G P torsion U N params p orientation t ≠ 0 :=
  div_ne_zero (balancedScalar_nonzero G P torsion U N params p orientation t)
    (phaseScalar_nonzero G P torsion U N params p (balancedPhase G P torsion U N params p orientation t))

variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
include sameBasis nonstandard
/-- Exact CURRENT source key, keeping its two original native-X edges. -/
theorem sourceConnection_normal (p orientation : Bool) (t : Phase N.m) :
    sourceConnection G P torsion U N params p orientation t =
      scale (phaseScalar G P torsion U N params p (balancedPhase G P torsion U N params p orientation t))
        (Kernel.mul (D (delta params))
          (if p then S (balancedPhase G P torsion U N params p orientation t).val
            else R (balancedPhase G P torsion U N params p orientation t).val)) := by
  unfold sourceConnection connectionKey
  rw [HistorySectorCards.map_mul,HistorySectorCards.map_mul,HistorySectorCards.map_X,
    Holant.Marked.SupportAtlas.effective_transport,Kernel.mul_assoc,transport_mul_edge]
  have he := (HistorySectorNormalized.phaseIndex G P torsion U N p
    (balancedPhase G P torsion U N params p orientation t)).transfer
  change sectorTransfer U (HistorySectorCards.mapBinary (algebraicEmbedding G)
    (actualRepresentative P.family torsion
      (HistorySectorNormalized.phaseIndex G P torsion U N p
        (balancedPhase G P torsion U N params p orientation t)).key)) = _ at he
  have hedge : sectorEdge U = scale params.edgeMultiplier (D (delta params)) := by
    simpa only [sameBasis] using marked_edge params nonstandard
  rw [he,hedge,scale_mul]
  rfl

/-- Every balanced standard connection has an actual original key and explicit
nonzero algebraic coefficient; no connection compiler is assumed. -/
theorem balanced_source_exact (p orientation : Bool) (t : Phase N.m) :
    Kernel.mul
      (Kernel.mul (WeightedGauge.diagonal (if orientation then delta params else 1))
        (Holant.Dihedral.CompatibleClosure.M p t.val))
      (WeightedGauge.diagonal (if orientation then 1 else delta params)) =
    scale (connectionScalar G P torsion U N params p orientation t)
      (sourceConnection G P torsion U N params p orientation t) := by
  rw [balanced_kernel,sourceConnection_normal G P torsion U N params sameBasis nonstandard]
  have hc := phaseScalar_nonzero G P torsion U N params p
    (balancedPhase G P torsion U N params p orientation t)
  funext a b
  simp only [scale,connectionScalar]
  field_simp [hc]

omit sameBasis nonstandard in
/-- The literal source binary, with both existing original-G physical programmes. -/
def connectionAccess (p orientation : Bool) (t : Phase N.m) :
    CurrentSignatureAccess G P ⟨2,Holant.Projective.BoundedTorsion.binarySignature
      (actualRepresentative P.family torsion (connectionKey G P torsion U N params p orientation t))⟩ :=
  HistorySectorNormalized.representativeAccess G P torsion U N p
    (balancedPhase G P torsion U N params p orientation t)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
