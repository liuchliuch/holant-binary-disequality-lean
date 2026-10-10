import Holant.Proofs.Closure.ClosureShiftedWeightedFamilyAssembly
import Holant.Proofs.Closure.ClosureStableFactorDescent

/-! Inverse transport of the SAME saved-anchor fixed binary. The port gauges
are inverted on the exact factor partition, then the original common basis is
inverted. Pivot descent recovers only the residual factor in ORIGINAL L,
retaining the literal selected original binary, exact ports and unit1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.EndpointParallelogram Holant.Dihedral.TwoCardLocalization
open ClosurePhysicalBridge ClosureCompatibleAlignment
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (A : SourceAnchor G P torsion U N params f order)
variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
variable (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
variable (large : 2 ≤ r)

def anchorOriginalBinary (e : Fin (r+1)) : Binary (K:=OI.K G) :=
  A.native.matrix ((finCongr (anchorEdgeCount G P torsion U N params f order A)).symm e)

def anchorOriginalTable (e : Fin (r+1)) : Signature (OI.K G) 2 :=
  fun x => anchorOriginalBinary G P torsion U N params f order A e (x 0) (x 1)

theorem savedNative :
    (selectSample G P torsion U N params f order A sameBasis nonstandard stable large
      (savedSample G P torsion U N params f order A sameBasis nonstandard stable large)).native = A.native := by
  simp [selectSample]

private theorem countAny (M : Presentation (OI.K G) (Fin (2*r+2))) : M.edges = r+1 := by
  have h := Fintype.card_congr M.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
  omega
private def portsAny (M : Presentation (OI.K G) (Fin (2*r+2))) : (Fin (r+1) × Bool) ≃ Fin (2*r+2) :=
  (Equiv.prodCongr (finCongr (countAny G M)).symm (Equiv.refl Bool)).trans M.ports
private def factorAny (M : Presentation (OI.K G) (Fin (2*r+2))) (weights : Fin (2*r+2) → Scalar)
    (e : Fin (r+1)) : Mat :=
  (gaugePresentation (HistorySectorCards.matching (algebraicEmbedding G) U M) weights).matrix
    ((finCongr (countAny G M)).symm e)

theorem savedPorts :
    selectionPorts G P torsion U N params f order A sameBasis nonstandard stable large
      (savedSample G P torsion U N params f order A sameBasis nonstandard stable large)
      (selectSample G P torsion U N params f order A sameBasis nonstandard stable large
        (savedSample G P torsion U N params f order A sameBasis nonstandard stable large)) =
      anchorPorts G P torsion U N params f order A := by
  change portsAny G
    (selectSample G P torsion U N params f order A sameBasis nonstandard stable large
      (savedSample G P torsion U N params f order A sameBasis nonstandard stable large)).native = portsAny G A.native
  exact congrArg (portsAny G) (savedNative G P torsion U N params f order A sameBasis nonstandard stable large)

theorem savedFactor (e : Fin (r+1)) :
    currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large
      (savedSample G P torsion U N params f order A sameBasis nonstandard stable large) e =
    Kernel.mul (transport U (HistorySectorCards.mapBinary (algebraicEmbedding G)
      (anchorOriginalBinary G P torsion U N params f order A e))) (D (delta params)) := by
  rw [currentFamilyTables,alignedTables,savedPorts]
  simp only [alignedFactor,edgeIndex,edgeReversed,Equiv.symm_apply_apply,Bool.false_eq_true,ite_false]
  change factorAny G U
    (selectSample G P torsion U N params f order A sameBasis nonstandard stable large
      (savedSample G P torsion U N params f order A sameBasis nonstandard stable large)).native
    (anchorWeights G P torsion U N params f order A) e = _
  have same := congrArg (fun M : Presentation (OI.K G) (Fin (2*r+2)) =>
    factorAny G U M (anchorWeights G P torsion U N params f order A) e)
    (savedNative G P torsion U N params f order A sameBasis nonstandard stable large)
  rw [same]
  simp only [factorAny,gaugePresentation,anchorWeights,rightWeights,HistorySectorCards.matching,
    Equiv.symm_apply_apply,Bool.false_eq_true,ite_false,ite_true]
  change Kernel.mul
    (Kernel.mul (WeightedGauge.diagonal 1)
      (transport U (HistorySectorCards.mapBinary (algebraicEmbedding G)
        (anchorOriginalBinary G P torsion U N params f order A e))))
    (WeightedGauge.diagonal (delta params)) = _
  have one : WeightedGauge.diagonal (1 : Scalar) = Signature.equality := by
    funext a b; cases a <;> cases b <;> rfl
  rw [one,Kernel.equality_mul]
  rfl

theorem anchor_original_nonzero (e : Fin (r+1)) : anchorOriginalTable G P torsion U N params f order A e ≠ 0 := by
  have group := actualTransfers_projectiveMatrixGroup P.family (actualTransfers_nonempty P.family) torsion
  have nonsingular := SafeBinary.nonsingular group (A.valid ((finCongr (anchorEdgeCount G P torsion U N params f order A)).symm e))
  obtain ⟨a,b,live⟩ := nonsingular_has_entry _ nonsingular
  intro zero
  have hz := congrFun zero (![a,b] : Fin 2 → Bool)
  exact live hz

theorem wholeWeights_nonzero : ∀ i,wholeWeights G P torsion U N params f order A i ≠ 0 := by
  intro i
  exact mul_ne_zero (firstWeights_nonzero _ (delta_ne_zero params) i)
    (liftWeights_nonzero _ (rightWeights_nonzero _ _ (delta_ne_zero params)) i)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
