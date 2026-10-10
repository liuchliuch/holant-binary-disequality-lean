import Holant.Proofs.Closure.HistorySectorNormalizedRepresentatives
import Holant.Proofs.Closure.ClosureSixPortCurrentAlgebraicCard
import Holant.Proofs.Closure.ClosureMarkedDihedralA0

/-! Actual all-arity A0-to-standard root cards. The fixed Hadamard basis, its
edge 2 diag(1,-1), and the derived even rotation order determine the phase
substitution. Every closure keeps its real CURRENT source key and literal
matching ports; the coordinate basis is never asserted to be a gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosurePhysicalBridge
open HistorySectorCardsAlgebra
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapSignature)
end RH
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (algebraicEmbedding G) P.family torsion))
abbrev basis := ClosureMarkedDihedralA0.basis

/-- Even order is derived by the actual A0 producer, so negation preserves roots. -/
theorem negative_root (t : Phase N.selected.m) : Roots N.selected.m (-t.val) := by
  unfold Roots at *
  rw [neg_pow,N.even.neg_one_pow,one_mul,t.property]

/-- The changed edge inverse is itself a standard root-group matrix. -/
theorem edgeInverse_mem : sectorEdgeInverse basis ∈ groupM N.selected.m := by
  have hi : sectorEdgeInverse basis = scale (1/2) (R (-1)) := by
    simpa [basis,ClosureMarkedDihedralA0.basis,ClosureMarkedCyclic.basis,R] using
      (edgeInverseA_eta (s:=1) (eta:=1) one_ne_zero (by simp : (1:Scalar)^2 = 1⁻¹))
  rw [hi]
  exact ⟨-1,(by unfold Roots; exact N.even.neg_one_pow),Or.inl ⟨1/2,(by norm_num),rfl⟩⟩

/-- Actual normalized transfer spectra and the real weighted edge imply
standard root-group BINARY TABLES for A0; this fails for shifted A in general. -/
theorem actual_table_mem (B : Binary (K:=OI.K G)) (actual : ActualNonsingular P.family B) :
    transport basis (HistorySectorCards.mapBinary (algebraicEmbedding G) B) ∈ groupM N.selected.m := by
  rw [transport_eq_transfer]
  exact groupM_mul (by have := N.range; omega)
    (ClosureMarkedDihedralA0.Source.actual_sector_spectrum
      (algebraicEmbedding G) P.family torsion N B actual) (edgeInverse_mem G P torsion N)

/-- The actual safe factor scalar remains the ORIGINAL field scalar. -/
theorem safe_table_mem (B : Binary (K:=OI.K G)) (safe : SafeBinary (actualTransfers P.family) B) :
    transport basis (HistorySectorCards.mapBinary (algebraicEmbedding G) B) ∈ groupM N.selected.m := by
  obtain ⟨C,actual,c,hc,hT⟩ := safe
  have hB : B = c • C := by
    have h := congrArg (fun T : Binary (K:=OI.K G) => T * X) hT
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using h
  have he : HistorySectorCards.mapBinary (algebraicEmbedding G) B =
      scale (algebraicEmbedding G c) (HistorySectorCards.mapBinary (algebraicEmbedding G) C) := by
    rw [hB]; funext a b; exact (algebraicEmbedding G).map_mul c (C a b)
  rw [he]
  have hs : transport basis (scale (algebraicEmbedding G c)
      (HistorySectorCards.mapBinary (algebraicEmbedding G) C)) =
      scale (algebraicEmbedding G c)
        (transport basis (HistorySectorCards.mapBinary (algebraicEmbedding G) C)) := by
    unfold transport
    rw [scale_mul_right,scale_mul_left]
  rw [hs]
  exact (groupM_is_group (by have := N.range; omega)).scale_mem _
    (actual_table_mem G P torsion N C actual) _ ((map_ne_zero _).mpr hc)

/-- The actual old matching presentation is mapped coefficientwise and acted
on at its SAME ports. The global source scalar is preserved literally. -/
theorem matching_algebraic {n : ℕ} (f : Signature (OI.K G) n)
    (matching : MatchingOrZero (actualTransfers P.family) f) :
    basis.symm.action (RH.mapSignature (algebraicEmbedding G) f) = 0 ∨
      ClosureSixPort.AlgebraicRootMatching N.selected.m
        (basis.symm.action (RH.mapSignature (algebraicEmbedding G) f)) := by
  rcases matching with hz | ⟨M,valid,scalar,rfl⟩
  · left
    rw [hz]
    have hm : RH.mapSignature (algebraicEmbedding G) (0 : Signature (OI.K G) n) = 0 := by
      funext x; exact map_zero _
    rw [hm,ClosureFactorTreeAction.action_zero]
  · exact Or.inr ⟨HistorySectorCards.matching (algebraicEmbedding G) basis M,
      fun e => safe_table_mem G P torsion N _ (valid e),
      (map_ne_zero (algebraicEmbedding G)).mpr scalar,
      HistorySectorCards.matching_tensor (algebraicEmbedding G) basis M⟩

def complexPresentation {n : ℕ} (M : Presentation Scalar (Fin n)) : Presentation ℂ (Fin n) where
  edges := M.edges
  ports := M.ports
  matrix e := (M.matrix e).map ClosureMarkedDihedral.inclusion
  scalar := ClosureMarkedDihedral.inclusion M.scalar

theorem complexPresentation_tensor {n : ℕ} (M : Presentation Scalar (Fin n)) :
    (complexPresentation M).tensor = RH.mapSignature ClosureMarkedDihedral.inclusion M.tensor := by
  funext x
  simp only [complexPresentation,Presentation.tensor,productValue,RH.mapSignature,
    Matrix.map_apply,map_mul,map_prod]
  rfl

theorem algebraic_matching_complex {n m : ℕ} (hm : 0 < m) (f : Signature Scalar n)
    (matching : f = 0 ∨ ClosureSixPort.AlgebraicRootMatching m f) :
    RH.mapSignature ClosureMarkedDihedral.inclusion f = 0 ∨
      ClosureSixPort.RootMatching m (RH.mapSignature ClosureMarkedDihedral.inclusion f) := by
  rcases matching with rfl | ⟨M,member,scalar,rfl⟩
  · left; funext x; exact map_zero _
  · right
    exact ⟨complexPresentation M,
      fun e => groupM_complex_root hm _ (member e),
      (map_ne_zero ClosureMarkedDihedral.inclusion).mpr scalar,
      (complexPresentation_tensor M).symm⟩

/-- Literal factor ports and source scalar survive both field maps. -/
theorem matching_map {n : ℕ} (f : Signature (OI.K G) n)
    (matching : MatchingOrZero (actualTransfers P.family) f) :
    RH.mapSignature ClosureMarkedDihedral.inclusion
      (basis.symm.action (RH.mapSignature (algebraicEmbedding G) f)) = 0 ∨
      ClosureSixPort.RootMatching N.selected.m
        (RH.mapSignature ClosureMarkedDihedral.inclusion
          (basis.symm.action (RH.mapSignature (algebraicEmbedding G) f))) :=
  algebraic_matching_complex (by have := N.range; omega) _
    (matching_algebraic G P torsion N f matching)

/-- Exact phase replacement forced by the A0 connection kernel. -/
def phase (p : Bool) (t : Phase N.selected.m) : Phase N.selected.m :=
  ⟨-(if p then t.val⁻¹ else t.val),by
    cases p
    · exact negative_root G P torsion N t
    · exact negative_root G P torsion N ⟨t.val⁻¹,t.property.inv⟩⟩

def index (p : Bool) (t : Phase N.selected.m) :=
  HistorySectorNormalized.phaseIndex G P torsion basis N.selected p (phase G P torsion N p t)

def cardScalar (p : Bool) (t : Phase N.selected.m) : Scalar :=
  2 * (index G P torsion N p t).multiplier * (if p then -t.val⁻¹ else 1)

theorem cardScalar_nonzero (p : Bool) (t : Phase N.selected.m) : cardScalar G P torsion N p t ≠ 0 := by
  have ht := t.property.ne_zero (by have := N.range; omega)
  exact mul_ne_zero (mul_ne_zero (by norm_num) (index G P torsion N p t).nonzero)
    (by cases p <;> simp [ht])

/-- Both native-X edges are transported; their scalar two is kept exactly. -/
theorem closingKernel (p : Bool) (t : Phase N.selected.m) :
    Kernel.pullback
      (HistorySectorCards.mapBinary (algebraicEmbedding G)
        (X * actualRepresentative P.family torsion (index G P torsion N p t).key * X)) basis.matrix =
      scale (cardScalar G P torsion N p t) (Holant.Dihedral.CompatibleClosure.M p t.val) := by
  rw [HistorySectorCards.map_mul,HistorySectorCards.map_mul,HistorySectorCards.map_X,
    effective_transport,Kernel.mul_assoc,transport_mul_edge]
  have he := (index G P torsion N p t).transfer
  change sectorTransfer basis (HistorySectorCards.mapBinary (algebraicEmbedding G)
    (actualRepresentative P.family torsion (index G P torsion N p t).key)) = _ at he
  rw [he,ClosureMarkedDihedralA0.NativeA0.same_edge,scale_mul]
  funext a b
  have ht := t.property.ne_zero (by have := N.range; omega)
  cases p <;> cases a <;> cases b <;>
    simp [cardScalar,index,phase,scale,diagonalKernel,R,S,Kernel.mul_apply,
      Signature.disequality,Holant.Dihedral.CompatibleClosure.M,Holant.Marked.monomial] <;>
    field_simp

set_option backward.isDefEq.respectTransparency false in
/-- Every ordered all-arity CURRENT raw key has its exact transformed root card. -/
theorem ordered_card_raw_scalar {n : ℕ} (f : Signature (OI.K G) (n+2))
    (e : Equiv.Perm (Fin (n+2))) (p : Bool) (t : Phase N.selected.m) :
    basis.symm.action (RH.mapSignature (algebraicEmbedding G)
      (rawCard P.family torsion f (DeckContraction.orderedKey P.family torsion e
        (index G P torsion N p t).key))) =
      cardScalar G P torsion N p t •
        Signature.contract (Holant.Dihedral.CompatibleClosure.M p t.val)
          (Tensor.reindex e.symm (basis.symm.action (RH.mapSignature (algebraicEmbedding G) f))) := by
  rw [DeckContraction.rawCard_ordered,HistorySectorCards.map_contract,contract_transport]
  have hr : RH.mapSignature (algebraicEmbedding G) (Tensor.reindex e.symm f) =
      Tensor.reindex e.symm (RH.mapSignature (algebraicEmbedding G) f) := rfl
  rw [hr,reindex_transport,closingKernel]
  funext x
  simp only [Signature.contract,scale,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureA0Stable
end
