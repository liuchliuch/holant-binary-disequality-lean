import Holant.Proofs.Closure.ClosureShiftedWeightedConnections

/-! Arbitrary original-port covariance for actual weighted localization.
Every balanced outside pair returns its literal CURRENT source closure key,
remaining gauge weights, nonzero coordinate multiplier and source-field table.
No tensor factor, compiler or successful localization is an extra input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge HistorySectorCardsAlgebra
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}

theorem gauge_reindex (r : Fin n → K) (e : Equiv.Perm (Fin n)) (f : Signature K n) :
    Tensor.reindex e (WeightedGauge.gauge r f) =
      WeightedGauge.gauge (fun i => r (e.symm i)) (Tensor.reindex e f) := by
  funext x
  unfold Tensor.reindex WeightedGauge.gauge WeightedGauge.weight
  congr 1
  simpa only [Equiv.symm_apply_apply] using
    Equiv.prod_comp e (fun j => WeightedGauge.bitWeight (r (e.symm j)) (x j))

theorem weight_first_two (r : Fin (n+2) → K) (a b : Bool) (x : Fin n → Bool) :
    WeightedGauge.weight r (Fin.cons a (Fin.cons b x)) =
      WeightedGauge.bitWeight (r 0) a * WeightedGauge.bitWeight (r 1) b *
        WeightedGauge.weight (fun j => r j.succ.succ) x := by
  simp [WeightedGauge.weight,Fin.prod_univ_succ,mul_assoc]

/-- Both deleted-port weights enter the exact ordered bilinear connection. -/
theorem full_contract_gauge (r : Fin (n+2) → K) (C : Kernel K) (f : Signature K (n+2)) :
    Signature.contract C (WeightedGauge.gauge r f) =
      WeightedGauge.gauge (fun j => r j.succ.succ)
        (Signature.contract (Kernel.mul (Kernel.mul (WeightedGauge.diagonal (r 0)) C)
          (WeightedGauge.diagonal (r 1))) f) := by
  funext x
  simp only [Signature.contract,WeightedGauge.gauge,weight_first_two,
    WeightedGauge.diagonal_mul,WeightedGauge.mul_diagonal,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))
variable (params : Parameters N.m) (h : Signature (OI.K G) (n+2))
variable (cut : Equiv.Perm (Fin (n+2)))

def outsideSource (p orientation : Bool) (t : Phase N.m) : Signature (OI.K G) n :=
  rawCard P.family torsion h (DeckContraction.orderedKey P.family torsion cut
    (connectionKey G P torsion U N params p orientation t))

/-- The outside contraction is the SAME original-L table and original order. -/
theorem outsideSource_transport (p orientation : Bool) (t : Phase N.m) :
    U.symm.action (RH.mapSignature (algebraicEmbedding G)
      (outsideSource G P torsion U N params h cut p orientation t)) =
      Signature.contract (sourceConnection G P torsion U N params p orientation t)
        (Tensor.reindex cut.symm (U.symm.action (RH.mapSignature (algebraicEmbedding G) h))) := by
  unfold outsideSource
  rw [DeckContraction.rawCard_ordered,HistorySectorCards.map_contract,contract_transport]
  have hr : RH.mapSignature (algebraicEmbedding G) (Tensor.reindex cut.symm h) =
      Tensor.reindex cut.symm (RH.mapSignature (algebraicEmbedding G) h) := rfl
  rw [hr,reindex_transport]
  rfl

variable (sameBasis : params.basis = U) (nonstandard : nonstandard params)
include sameBasis nonstandard
/-- Every balanced standard closure has its actual source phase/key preimage,
remaining ORIGINAL port order and separate nonzero coordinate coefficient. -/
theorem balanced_pair_covariance (r : Fin (n+2) → Scalar) (p orientation : Bool) (t : Phase N.m)
    (first : r (cut 0) = if orientation then delta params else 1)
    (second : r (cut 1) = if orientation then 1 else delta params) :
    Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
      (Tensor.reindex cut.symm
        (WeightedGauge.gauge r (U.symm.action (RH.mapSignature (algebraicEmbedding G) h)))) =
      connectionScalar G P torsion U N params p orientation t •
        WeightedGauge.gauge (fun j => r (cut j.succ.succ))
          (U.symm.action (RH.mapSignature (algebraicEmbedding G)
            (outsideSource G P torsion U N params h cut p orientation t))) := by
  rw [gauge_reindex,full_contract_gauge]
  simp only [Equiv.symm_symm]
  rw [first,second,balanced_source_exact G P torsion U N params sameBasis nonstandard]
  rw [outsideSource_transport]
  funext x
  simp only [WeightedGauge.gauge,Signature.contract,scale,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit sameBasis nonstandard in
/-- The canonical right-endpoint gauge gives balanced connections between
ANY two selected original matching edges, with both actual ports retained. -/
theorem matching_cross_weights (M : Presentation Scalar (Fin (n+2))) (d : Scalar)
    (e f : Fin M.edges) :
    let cut := ClosureStableFactor.pairOrder (M.ports (e,true)) (M.ports (f,false))
    rightWeights M d (cut 0) = d ∧ rightWeights M d (cut 1) = 1 := by
  dsimp only
  have distinct : M.ports (e,true) ≠ M.ports (f,false) := by
    intro equal
    have bits := congrArg Prod.snd (M.ports.injective equal)
    cases bits
  rw [ClosureStableFactor.pairOrder_first _ _ distinct,ClosureStableFactor.pairOrder_second]
  simp [rightWeights]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
