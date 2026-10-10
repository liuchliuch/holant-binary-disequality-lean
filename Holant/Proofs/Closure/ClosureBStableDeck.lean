import Holant.Proofs.Closure.ClosureBStableMatrix
import Holant.Proofs.Closure.HistorySectorNormalizedRepresentatives
import Holant.Proofs.Closure.ClosureSixPortCurrentAlgebraicCard

/-! All-arity standard-M cards derived from a literal CURRENT B marking.
The source keys, ordered ports, nonzero source and coordinate multipliers,
and the exact changed edge remain explicit. No sector deck is an input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

def normalizedModel : ClosureMarkedDihedral.NativeM
    (ClosureMarkedDihedralCoordinates.normalized basisB
      (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion)) := N.selected

def phaseIndex (p : Bool) (t : {t : Scalar // Roots N.selected.m t}) :=
  HistorySectorNormalized.phaseIndex G P torsion basisB (normalizedModel G P torsion N)
    p (phaseFor p t)

def cardCoefficient (p : Bool) (t : {t : Scalar // Roots N.selected.m t}) : Scalar :=
  edgeScalar * (phaseIndex G P torsion N p t).multiplier / phaseScalar p t

theorem cardCoefficient_nonzero (p : Bool) (t : {t : Scalar // Roots N.selected.m t}) :
    cardCoefficient G P torsion N p t≠0 :=
  div_ne_zero (mul_ne_zero edgeScalar_nonzero (phaseIndex G P torsion N p t).nonzero)
    (phaseScalar_nonzero (by have := N.selected.range; omega) p t)

def currentKernel (p : Bool) (t : {t : Scalar // Roots N.selected.m t}) : Binary (K:=OI.K G) :=
  X * actualRepresentative P.family torsion (phaseIndex G P torsion N p t).key * X

theorem currentKernel_exact (p : Bool) (t : {t : Scalar // Roots N.selected.m t}) :
    Kernel.pullback (HistorySectorCards.mapBinary (ClosureSourceRows.embedding G)
      (currentKernel G P torsion N p t)) basisB.matrix=
        scale (cardCoefficient G P torsion N p t) (M p t.val) := by
  rw [currentKernel,HistorySectorCards.map_mul,HistorySectorCards.map_mul,
    HistorySectorCards.map_X,Holant.Marked.SupportAtlas.effective_transport,effective_kernel]
  have phase := (phaseIndex G P torsion N p t).transfer
  change sectorTransfer basisB
    (HistorySectorCards.mapBinary (ClosureSourceRows.embedding G)
      (actualRepresentative P.family torsion (phaseIndex G P torsion N p t).key)) = _ at phase
  rw [phase,phase_order (by have := N.selected.range; omega)]
  funext u v
  simp only [scale,cardCoefficient]
  field_simp [phaseScalar_nonzero (by have := N.selected.range; omega) p t]
  rfl

def transformed {n : ℕ} (f : Signature (OI.K G) n) : Signature Scalar n :=
  basisB.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)

/-- The native source contraction is transformed with the weighted edge;
only the proved B substitutions then turn it into the standard M card. -/
theorem ordered_card_identity {n : ℕ} (f : Signature (OI.K G) (n+2))
    (order : Equiv.Perm (Fin (n+2))) (p : Bool) (t : {t : Scalar // Roots N.selected.m t}) :
    basisB.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (rawCard P.family torsion f (DeckContraction.orderedKey P.family torsion order
        (phaseIndex G P torsion N p t).key))) =
      cardCoefficient G P torsion N p t • Signature.contract (M p t.val)
        (Tensor.reindex order.symm (transformed G f)) := by
  rw [DeckContraction.rawCard_ordered]
  change basisB.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
    (Signature.contract (currentKernel G P torsion N p t) (Tensor.reindex order.symm f))) = _
  rw [HistorySectorCards.map_contract,HistorySectorCardsAlgebra.contract_transport,currentKernel_exact]
  have reindex : RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (Tensor.reindex order.symm f)=
      Tensor.reindex order.symm (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f) := rfl
  rw [reindex,HistorySectorCardsAlgebra.reindex_transport]
  funext x
  simp only [Signature.contract,scale,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool,transformed]
  ring

theorem safe_transformed_groupM (B : Binary (K:=OI.K G)) (safe : SafeBinary (actualTransfers P.family) B) :
    transport basisB (HistorySectorCards.mapBinary (ClosureSourceRows.embedding G) B) ∈ groupM N.selected.m := by
  have witness : ∃ C : Binary (K:=OI.K G),ActualNonsingular P.family C ∧
      ∃ c : OI.K G,c≠0 ∧ transfer B=c • transfer C := safe
  obtain ⟨C,actual,c,cn,equation⟩ := witness
  have literal : B=c • C := by
    have h := congrArg (fun T : Binary (K:=OI.K G) => T*X) equation
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using h
  have spectrum := ClosureMarkedDihedralB.Source.actual_sector_spectrum
    (ClosureSourceRows.embedding G) P.family torsion N C actual
  have base : transport basisB (HistorySectorCards.mapBinary (ClosureSourceRows.embedding G) C)=
      scale (imaginaryUnit/2) (sectorTransfer basisB (Matrix.map C (ClosureSourceRows.embedding G))) := by
    rw [transport_eq_transfer,edgeInverseB,scale_mul_right,Kernel.mul_equality]
    rfl
  have baseMember : transport basisB (HistorySectorCards.mapBinary (ClosureSourceRows.embedding G) C)
      ∈ groupM N.selected.m := by
    rw [base]
    exact (groupM_is_group (by have := N.selected.range; omega)).scale_mem _ spectrum _
      (div_ne_zero imaginaryUnit_ne_zero (by norm_num))
  have scalar : transport basisB (HistorySectorCards.mapBinary (ClosureSourceRows.embedding G) B)=
      scale (ClosureSourceRows.embedding G c)
        (transport basisB (HistorySectorCards.mapBinary (ClosureSourceRows.embedding G) C)) := by
    rw [literal]
    funext u v
    simp only [transport,HistorySectorCards.mapBinary,Matrix.smul_apply,smul_eq_mul,map_mul,
      Kernel.mul_apply,Kernel.transpose_apply,scale]
    ring
  rw [scalar]
  exact (groupM_is_group (by have := N.selected.range; omega)).scale_mem _ baseMember _ ((map_ne_zero _).mpr cn)

theorem matching_factor_groupM {n : ℕ} (Q : Presentation (OI.K G) (Fin n))
    (valid : Q.Valid (actualTransfers P.family)) (e : Fin Q.edges) :
    (HistorySectorCards.matching (ClosureSourceRows.embedding G) basisB Q).matrix e ∈ groupM N.selected.m :=
  safe_transformed_groupM G P torsion N _ (valid e)

theorem transformed_matching {n : ℕ} (f : Signature (OI.K G) n)
    (matching : MatchingOrZero (actualTransfers P.family) f) :
    transformed G f=0 ∨ ClosureSixPort.AlgebraicRootMatching N.selected.m (transformed G f) := by
  rcases matching with zero | ⟨Q,valid,scalar,equation⟩
  · left
    rw [zero]
    have mapped : RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (0 : Signature (OI.K G) n)=0 := by
      funext x; exact map_zero _
    rw [transformed,mapped,ClosureFactorTreeAction.action_zero]
  · right
    refine ⟨HistorySectorCards.matching (ClosureSourceRows.embedding G) basisB Q,
      matching_factor_groupM G P torsion N Q valid,
      (map_ne_zero _).mpr scalar,?_⟩
    rw [equation]
    exact HistorySectorCards.matching_tensor _ _ _

theorem algebraicRootMatching_scale {n m : ℕ} {q : Signature Scalar n}
    (actual : ClosureSixPort.AlgebraicRootMatching m q) (c : Scalar) (nonzero : c≠0) :
    ClosureSixPort.AlgebraicRootMatching m (c • q) := by
  obtain ⟨Q,member,scalar,equation⟩ := actual
  refine ⟨{Q with scalar := c*Q.scalar},member,mul_ne_zero nonzero scalar,?_⟩
  rw [equation]
  funext x
  simp only [Presentation.tensor,Holant.Certificates.MatchingContractionClosure.productValue,Pi.smul_apply,smul_eq_mul]
  ring

/-- All original orders and both phase sectors inherit a genuine zero-safe
standard-M deck from the actual CURRENT B deck. -/
theorem ordered_root_deck {n : ℕ} (f : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
    (order : Equiv.Perm (Fin (n+2))) (p : Bool) (t : {t : Scalar // Roots N.selected.m t}) :
    Signature.contract (M p t.val) (Tensor.reindex order.symm (transformed G f))=0 ∨
      ClosureSixPort.AlgebraicRootMatching N.selected.m
        (Signature.contract (M p t.val) (Tensor.reindex order.symm (transformed G f))) := by
  let key := DeckContraction.orderedKey P.family torsion order (phaseIndex G P torsion N p t).key
  have original := transformed_matching G P torsion N _ (stable _ (Or.inr ⟨key,rfl⟩))
  have identity := ordered_card_identity G P torsion N f order p t
  have live := cardCoefficient_nonzero G P torsion N p t
  change transformed G (rawCard P.family torsion f key)=_ at identity
  rw [identity] at original
  rcases original with zero | actual
  · exact Or.inl ((smul_eq_zero.mp zero).resolve_left live)
  · right
    have scaled := algebraicRootMatching_scale actual (cardCoefficient G P torsion N p t)⁻¹ (inv_ne_zero live)
    simpa only [smul_smul,inv_mul_cancel₀ live,one_smul] using scaled

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureBStable
