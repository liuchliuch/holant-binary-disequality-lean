import Holant.Proofs.Closure.HistorySectorNormalizedDeck
import Holant.Proofs.Closure.DeckContraction

/-! All-arity CURRENT weighted root-card domain at the SAME constructed
marked basis. The actual phase key, original-field factor presentation and
separate nonzero coordinate scalar are preserved. No newly generated native-X
sector deck or common port gauge is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge HistorySectorCardsAlgebra
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapSignature)
end RH
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family) (U : InvertibleKernel)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedralCoordinates.normalized U
    (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion)))

private theorem map_scale (B : Binary (K:=OI.K G)) (c : OI.K G) :
    HistorySectorCards.mapBinary (algebraicEmbedding G) (fun a b => c * B a b) =
      scale (algebraicEmbedding G c) (HistorySectorCards.mapBinary (algebraicEmbedding G) B) := by
  funext a b
  exact (algebraicEmbedding G).map_mul c (B a b)

/-- Every literal safe source factor has the actual weighted standard transfer. -/
theorem safe_factor_transfer (B : Binary (K:=OI.K G))
    (safe : SafeBinary (actualTransfers P.family) B) :
    Kernel.mul (transport U (HistorySectorCards.mapBinary (algebraicEmbedding G) B))
      (sectorEdge U) ∈ groupM N.m := by
  obtain ⟨C,actual,c,hc,hT⟩ := safe
  have hB : B = (fun a b => c * C a b) := by
    have h := congrArg (fun T : Binary (K:=OI.K G) => T * X) hT
    simp only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] at h
    funext a b
    simpa only [Matrix.smul_apply,smul_eq_mul] using congrFun (congrFun h a) b
  rw [transport_mul_edge,hB,map_scale]
  have he : sectorTransfer U (scale (algebraicEmbedding G c)
      (HistorySectorCards.mapBinary (algebraicEmbedding G) C)) =
      scale (algebraicEmbedding G c)
        (sectorTransfer U (HistorySectorCards.mapBinary (algebraicEmbedding G) C)) := by
    rw [sectorTransfer,scale_mul_left,conjugate_scale]
    rfl
  rw [he]
  exact (groupM_is_group (by have := N.range; omega)).scale_mem _
    (ClosureMarkedDihedralCoordinates.Source.actual_sector_spectrum U
      (algebraicEmbedding G) P.family torsion N C actual) _ ((map_ne_zero _).mpr hc)

/-- The ORIGINAL literal presentation is retained as witness, alongside the
separate coordinate coefficient; matrix factors use the actual sector edge. -/
def WeightedProduct {n : ℕ} (g : Signature Scalar n) : Prop :=
  g = 0 ∨ ∃ M : Presentation (OI.K G) (Fin n), M.Valid (actualTransfers P.family) ∧
    M.scalar ≠ 0 ∧ ∃ c : Scalar, c ≠ 0 ∧
      g = c • (HistorySectorCards.matching (algebraicEmbedding G) U M).tensor ∧
      ∀ e, Kernel.mul ((HistorySectorCards.matching (algebraicEmbedding G) U M).matrix e)
        (sectorEdge U) ∈ groupM N.m

theorem matching_weighted {n : ℕ} (f : Signature (OI.K G) n)
    (matching : MatchingOrZero (actualTransfers P.family) f) :
    WeightedProduct G P torsion U N (U.symm.action (RH.mapSignature (algebraicEmbedding G) f)) := by
  rcases matching with hz | ⟨M,valid,scalar,rfl⟩
  · left
    rw [hz]
    have he : RH.mapSignature (algebraicEmbedding G) (0 : Signature (OI.K G) n) = 0 := by
      funext x; exact map_zero _
    rw [he,ClosureFactorTreeAction.action_zero]
  · right
    refine ⟨M,valid,scalar,1,one_ne_zero,?_,?_⟩
    · rw [one_smul,HistorySectorCards.matching_tensor]
    · intro e
      exact safe_factor_transfer G P torsion U N _ (valid e)

/-- Nonzero coordinate rescaling changes only the separate output coefficient. -/
theorem weighted_scale {n : ℕ} (f : Signature Scalar n) (c : Scalar) (hc : c ≠ 0)
    (weighted : WeightedProduct G P torsion U N f) : WeightedProduct G P torsion U N (c • f) := by
  rcases weighted with hz | ⟨M,valid,scalar,d,hd,he,hfactors⟩
  · left; rw [hz,smul_zero]
  · right
    exact ⟨M,valid,scalar,c*d,mul_ne_zero hc hd,by rw [he,smul_smul],hfactors⟩

variable (params : Parameters N.m) (sameBasis : params.basis = U)
variable (nonstandard : nonstandard params)

/-- Exact source key selected by the actual normalized group; attachments are empty. -/
def phaseKey {n : ℕ} (e : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.m) :
    RawCardKey n (completeGroup P.family torsion) :=
  DeckContraction.orderedKey P.family torsion e
    (HistorySectorNormalized.phaseIndex G P torsion U N p t).key

def phaseScalar (p : Bool) (t : Phase N.m) : Scalar :=
  params.edgeMultiplier * (HistorySectorNormalized.phaseIndex G P torsion U N p t).multiplier

theorem phaseScalar_nonzero (p : Bool) (t : Phase N.m) : phaseScalar G P torsion U N params p t ≠ 0 :=
  mul_ne_zero params.edgeMultiplier_ne_zero
    (HistorySectorNormalized.phaseIndex G P torsion U N p t).nonzero

/-- The weighted connection kernel, not a fresh X-native kernel. -/
def rootCard {n : ℕ} (f : Signature (OI.K G) (n+2)) (e : Equiv.Perm (Fin (n+2)))
    (p : Bool) (t : Phase N.m) : Signature Scalar n :=
  Signature.contract (Kernel.mul (diagonalKernel 1 (delta params)) (if p then S t.val else R t.val))
    (Tensor.reindex e.symm (U.symm.action (RH.mapSignature (algebraicEmbedding G) f)))

include sameBasis nonstandard
/-- All arities, both parities and every actual phase keep exact port order and scalar. -/
theorem rootCard_exact {n : ℕ} (f : Signature (OI.K G) (n+2))
    (e : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.m) :
    U.symm.action (RH.mapSignature (algebraicEmbedding G)
      (rawCard P.family torsion f (phaseKey G P torsion U N e p t))) =
      phaseScalar G P torsion U N params p t • rootCard G P torsion U N params f e p t := by
  unfold phaseKey
  rw [DeckContraction.rawCard_ordered,HistorySectorCards.map_contract,contract_transport]
  have hr : RH.mapSignature (algebraicEmbedding G) (Tensor.reindex e.symm f) =
      Tensor.reindex e.symm (RH.mapSignature (algebraicEmbedding G) f) := rfl
  rw [hr,reindex_transport]
  have hk : Kernel.pullback (HistorySectorCards.mapBinary (algebraicEmbedding G)
      (X * actualRepresentative P.family torsion (HistorySectorNormalized.phaseIndex G P torsion U N p t).key * X))
      U.matrix = scale (phaseScalar G P torsion U N params p t)
        (Kernel.mul (diagonalKernel 1 (delta params)) (if p then S t.val else R t.val)) := by
    rw [HistorySectorCards.map_mul,HistorySectorCards.map_mul,HistorySectorCards.map_X,
      effective_transport,Kernel.mul_assoc,transport_mul_edge]
    have he := (HistorySectorNormalized.phaseIndex G P torsion U N p t).transfer
    change sectorTransfer U (HistorySectorCards.mapBinary (algebraicEmbedding G)
      (actualRepresentative P.family torsion (HistorySectorNormalized.phaseIndex G P torsion U N p t).key)) = _ at he
    have hedge : sectorEdge U = scale params.edgeMultiplier (diagonalKernel 1 (delta params)) := by
      simpa only [sameBasis] using marked_edge params nonstandard
    rw [he,hedge,scale_mul]
    rfl
  rw [hk]
  unfold rootCard
  funext x
  simp only [Signature.contract,scale,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Closed higher-arity weighted domain, derived from the genuine CURRENT deck. -/
theorem rootCard_weighted {n : ℕ} (f : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion f, MatchingOrZero (actualTransfers P.family) g)
    (e : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.m) :
    WeightedProduct G P torsion U N (rootCard G P torsion U N params f e p t) := by
  have h := matching_weighted G P torsion U N _
    (stable _ (Or.inr ⟨phaseKey G P torsion U N e p t,rfl⟩))
  rw [rootCard_exact G P torsion U N params sameBasis nonstandard f e p t] at h
  have hi := weighted_scale G P torsion U N _ (phaseScalar G P torsion U N params p t)⁻¹
    (inv_ne_zero (phaseScalar_nonzero G P torsion U N params p t)) h
  simpa only [smul_smul,inv_mul_cancel₀ (phaseScalar_nonzero G P torsion U N params p t),one_smul] using hi

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted
end
