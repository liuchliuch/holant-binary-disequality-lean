import Holant.Proofs.Closure.ClosureShiftedWeightedOriginal

/-! Concrete ORIGINAL-field split of the SAME higher CURRENT source. The
selected original binary and exact original partition survive inverse port
gauges, inverse common basis and pivot descent. Only the residual table is
recovered in L; no desired split, factor access or new coefficient field is input. -/
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

def fixedPorts (e : Fin (r+1)) : Fin 2 ⊕ Fin (2*r+2) ≃ Fin (2*r+4) :=
  (factorPorts (2*r)).trans (ClosureStableFactor.liftResidual
    ((assembledFamily G P torsion U N params f order A sameBasis nonstandard stable large).residualOrder e))

theorem fixedPorts_zero (e : Fin (r+1)) :
    fixedPorts G P torsion U N params f order A sameBasis nonstandard stable large e (.inl 0) =
      (anchorPorts G P torsion U N params f order A (e,false)).succ.succ := by
  change (ClosureStableFactor.pairOrder
    (anchorPorts G P torsion U N params f order A (e,false))
    (anchorPorts G P torsion U N params f order A (e,true)) 0).succ.succ = _
  rw [ClosureStableFactor.pairOrder_first _ _ (port_distinct _ e)]

theorem fixedPorts_one (e : Fin (r+1)) :
    fixedPorts G P torsion U N params f order A sameBasis nonstandard stable large e (.inl 1) =
      (anchorPorts G P torsion U N params f order A (e,true)).succ.succ := by
  change (ClosureStableFactor.pairOrder
    (anchorPorts G P torsion U N params f order A (e,false))
    (anchorPorts G P torsion U N params f order A (e,true)) 1).succ.succ = _
  rw [ClosureStableFactor.pairOrder_second]

/-- The inverse at each actual fixed-factor port is computed, not supplied. -/
theorem inverse_left_factor (e : Fin (r+1)) :
    Signature.coordinateAction
      (fun i => WeightedGauge.diagonal ((wholeWeights G P torsion U N params f order A
        (fixedPorts G P torsion U N params f order A sameBasis nonstandard stable large e (.inl i)))⁻¹))
      (kernelSignature (currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large
        (savedSample G P torsion U N params f order A sameBasis nonstandard stable large) e)) =
    kernelSignature (transport U (HistorySectorCards.mapBinary (algebraicEmbedding G)
      (anchorOriginalBinary G P torsion U N params f order A e))) := by
  rw [←gauge_coordinate,savedFactor]
  have weights : (fun i : Fin 2 => (wholeWeights G P torsion U N params f order A
      (fixedPorts G P torsion U N params f order A sameBasis nonstandard stable large e (.inl i)))⁻¹) =
      ![(1 : Scalar),(delta params)⁻¹] := by
    funext i
    fin_cases i
    · change (wholeWeights G P torsion U N params f order A
        (fixedPorts G P torsion U N params f order A sameBasis nonstandard stable large e (.inl 0)))⁻¹ = 1
      rw [fixedPorts_zero,wholeWeights_tail,anchorWeights_port]
      simp
    · change (wholeWeights G P torsion U N params f order A
        (fixedPorts G P torsion U N params f order A sameBasis nonstandard stable large e (.inl 1)))⁻¹ = (delta params)⁻¹
      rw [fixedPorts_one,wholeWeights_tail,anchorWeights_port]
      rfl
  rw [weights]
  funext x
  simp [WeightedGauge.gauge,WeightedGauge.weight,Fin.prod_univ_succ,WeightedGauge.bitWeight,
    kernelSignature,Kernel.mul_apply,D,diagonalKernel,delta_ne_zero params]
  cases x 0 <;> cases x 1 <;> simp [Kernel.mul_apply,D,diagonalKernel,delta_ne_zero params,
    mul_comm,mul_left_comm,mul_assoc]

/-- The real shared assembly split descends with the exact original selected
binary, original port partition and literal source unit1. -/
theorem current_original_split :
    ∃ e : Fin (r+1),∃ R : Signature (OI.K G) (2*r+2),∃ S : ProperSplit
      (⟨2*r+4,f⟩ : AnySignature (OI.K G))
      ⟨2,anchorOriginalTable G P torsion U N params f order A e⟩ ⟨2*r+2,R⟩,
      S.ports = (fixedPorts G P torsion U N params f order A sameBasis nonstandard stable large e).trans order ∧
      S.scale = 1 := by
  obtain ⟨e,R,split,ports,unit⟩ := currentStandard_split G P torsion U N params f order A sameBasis nonstandard stable large
  let W := wholeWeights G P torsion U N params f order A
  let B := currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large
    (savedSample G P torsion U N params f order A sameBasis nonstandard stable large) e
  let inverseRight := Signature.coordinateAction
    (fun i => WeightedGauge.diagonal ((W (split.ports (.inr i)))⁻¹)) R
  have inverseRoot : Signature.coordinateAction (fun i => WeightedGauge.diagonal ((W i)⁻¹))
      (currentStandard G P torsion U N params f order A sameBasis nonstandard stable large) =
      Tensor.reindex order.symm (U.symm.action (RH.mapSignature (algebraicEmbedding G) f)) := by
    rw [←gauge_coordinate]
    change WeightedGauge.gauge (fun i => (W i)⁻¹)
      (WeightedGauge.gauge (firstWeights (delta params))
        (WeightedGauge.gauge (liftWeights (anchorWeights G P torsion U N params f order A)) _)) = _
    rw [WeightedGauge.gauge_comp (firstWeights (delta params))
      (liftWeights (anchorWeights G P torsion U N params f order A))]
    exact WeightedGauge.gauge_inverse W (wholeWeights_nonzero G P torsion U N params f order A) _
  have exactSplit := congrArg (Signature.coordinateAction (fun i => WeightedGauge.diagonal ((W i)⁻¹))) split.equation
  have hu : (split.scale : Scalar) = 1 := by rw [unit]; rfl
  rw [inverseRoot] at exactSplit
  change _ = Signature.coordinateAction _ (fun x => (split.scale : Scalar) *
    Tensor.reindex split.ports (Tensor.tensor (kernelSignature B) R) x) at exactSplit
  rw [hu] at exactSplit
  simp only [one_mul] at exactSplit
  rw [ClosureFactorTreeAction.coordinateAction_tensor] at exactSplit
  have left : Signature.coordinateAction
      (fun i => WeightedGauge.diagonal ((W (split.ports (.inl i)))⁻¹)) (kernelSignature B) =
      U.symm.action (RH.mapSignature (algebraicEmbedding G)
        (anchorOriginalTable G P torsion U N params f order A e)) := by
    rw [ports]
    change Signature.coordinateAction
      (fun i => WeightedGauge.diagonal ((wholeWeights G P torsion U N params f order A
        (fixedPorts G P torsion U N params f order A sameBasis nonstandard stable large e (.inl i)))⁻¹))
      (kernelSignature (currentFamilyTables G P torsion U N params f order A sameBasis nonstandard stable large
        (savedSample G P torsion U N params f order A sameBasis nonstandard stable large) e)) = _
    rw [inverse_left_factor]
    exact (transport_signature U (HistorySectorCards.mapBinary (algebraicEmbedding G)
      (anchorOriginalBinary G P torsion U N params f order A e))).symm
  rw [left] at exactSplit
  have reordered : U.symm.action (RH.mapSignature (algebraicEmbedding G) f) =
      Tensor.reindex (split.ports.trans order) (Tensor.tensor
        (U.symm.action (RH.mapSignature (algebraicEmbedding G)
          (anchorOriginalTable G P torsion U N params f order A e))) inverseRight) := by
    funext x
    have h := congrFun exactSplit (fun j => x (order j))
    simpa only [Tensor.reindex,Equiv.apply_symm_apply,Equiv.trans_apply,inverseRight] using h
  have acted := congrArg U.action reordered
  rw [U.action_symm_action] at acted
  change _ = Signature.coordinateAction (fun _ => U.matrix)
    (Tensor.reindex _ (Tensor.tensor _ inverseRight)) at acted
  rw [ClosureFactorTreeAction.coordinateAction_tensor] at acted
  change RH.mapSignature (algebraicEmbedding G) f =
    Tensor.reindex (split.ports.trans order) (Tensor.tensor
      (U.action (U.symm.action (RH.mapSignature (algebraicEmbedding G)
        (anchorOriginalTable G P torsion U N params f order A e)))) (U.action inverseRight)) at acted
  rw [U.action_symm_action] at acted
  let originalMapped : ProperSplit
      (mapSignature (algebraicEmbedding G) (⟨2*r+4,f⟩ : AnySignature (OI.K G)))
      (mapSignature (algebraicEmbedding G)
        (⟨2,anchorOriginalTable G P torsion U N params f order A e⟩ : AnySignature (OI.K G)))
      ⟨2*r+2,U.action inverseRight⟩ := {
    left_pos := by change 0 < 2; omega
    right_pos := by change 0 < 2*r+2; omega
    ports := split.ports.trans order
    scale := 1
    equation := by
      change RH.mapSignature (algebraicEmbedding G) f = fun x => (1 : Scalar) *
        Tensor.reindex (split.ports.trans order) (Tensor.tensor
          (RH.mapSignature (algebraicEmbedding G) (anchorOriginalTable G P torsion U N params f order A e))
          (U.action inverseRight)) x
      simpa only [one_mul] using acted }
  obtain ⟨right,result,exactPorts,exactUnit⟩ := ClosureStableFactor.known_left_descends (algebraicEmbedding G) f
    (anchorOriginalTable G P torsion U N params f order A e)
    (anchor_original_nonzero G P torsion U N params f order A e) _ originalMapped
  refine ⟨e,right,result,?_,exactUnit⟩
  rw [exactPorts]
  change split.ports.trans order = _
  rw [ports]
  rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
