import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseEq4Product
import Holant.Proofs.Hardness.GeneralEOAffineNetworkField

/-! A sparse affine prime quaternary supplies a genuine equality-four graph.
The nonproduct plane is repeated 24 times with the original field, original
palette labels and native-X edges. The scalar period is derived, not assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionAffineAncestorEq4
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Marked.SupportAtlas
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open StableCurrentEvenEOTransport StableCurrentEvenLocalOutcome StableCurrentEvenEOTract
namespace B
export EOBinaryPlaneCore (compress normalized normalized_lift)
end B
namespace A
export GeneralEOAffineNetworkChain (network labels exact native power_denote)
end A
namespace F
export GeneralEOAffineNetworkField.Mapped (scale scale_nonzero power)
end F
namespace S
export GlobalCloseCompletionSparseEq4Product (labels exact)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

/-- A binary affine signature which is not Product has all four entries.
The small-support and three-support alternatives are excluded explicitly. -/
theorem binary_full (f : Signature AlgebraicComplex 2) (ha : Affine f) (hp : ¬Product f) :
    EOBinaryPlaneClassification.Full f := by
  classical
  have large : 2<(EOQuaternarySparseTract.support f).card := by
    by_contra h
    exact hp (EOQuaternarySparseTract.binary_small f (by omega))
  intro x hx
  have subset : EOQuaternarySparseTract.support f ⊆ Finset.univ.erase x := by
    intro y hy
    apply Finset.mem_erase.mpr
    exact ⟨fun h => (EOQuaternarySparseTract.mem_support f y).mp hy (h ▸ hx),Finset.mem_univ y⟩
  have bound := Finset.card_le_card subset
  have card : (Finset.univ.erase x : Finset (Fin 2 → Bool)).card=3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x)]
    decide
  rw [card] at bound
  exact EOBinaryPlaneClassification.three_not_affine f (by omega) ha

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)
variable (d : SparseOutput G P q core literal)

include torsion N core literal stable d in
/-- This is the full Affine branch, including its Product overlap. There is
no supplied matrix period, generalized equality, or additional gate. -/
theorem produce (affine : Affine (embedded G q)) :
    Nonempty (GlobalCloseCompletionEq4Graph.Output G P) := by
  classical
  by_cases product : Product (embedded G q)
  · exact GlobalCloseCompletionSparseEq4Product.produce G P q core literal d product
  let M := eoRow G P q core literal d
  have hA : Affine M := by
    change Affine (eoRow G P q core literal d)
    rw [eoRow_exact]
    exact class_flip .affine (embedded G q) d.mask affine
  have hP : ¬Product M := by
    intro hp
    change Product (eoRow G P q core literal d) at hp
    rw [eoRow_exact] at hp
    exact product (class_unflip .product (embedded G q) d.mask hp)
  have eo := eoRow_support G P q core literal d
  have closed := eoRow_complement_closed G P torsion N q core literal stable d
  obtain ⟨i,zero⟩ := missing_middle_of_supports M eo .positive
    (fun x y z hx hy hz => Or.inl (affine_support_xor3 hA x y z hx hy hz))
  have opposite : FiveSupportEOOrdering.middleCoeff M (5-i)=0 := by
    rw [FiveSupportEOOrdering.middleCoeff,←middleWord_complement]
    exact (closed (FiveSupportEOOrdering.middleWord i)).mpr zero
  let e := FiveSupportEOOrdering.orderAt i
  let f := B.compress (B.normalized M i)
  have plane : EOBinaryPlaneCore.lift f=Tensor.reindex e M := B.normalized_lift M eo i zero opposite
  have fa : Affine f := by
    have h := hA.precompose (EOBinaryPlaneTract.transportPairing e EOBinaryPlaneCore.pairing).word
      (EOBinaryPlaneTract.pairing_affine _)
    change Affine ((EOBinaryPlaneTract.transportPairing e EOBinaryPlaneCore.pairing).restrict M) at h
    rw [EOBinaryPlaneTract.restriction_reindex,EOBinaryPlaneCore.restrict_eq] at h
    exact h
  have fp : ¬Product f := by
    intro hp
    have h := EOBinaryPlaneTract.product_lift hp
    rw [plane] at h
    exact hP (EOBinaryPlaneTract.product_unreindex e M h)
  have full := binary_full f fa fp
  let original := B.compress (Tensor.reindex e d.access.source.denote)
  have mapped (x : Fin 4 → Bool) :
      (ClosureSourceRows.embedding G) (d.access.source.denote x)=M x := by
    rw [←d.access.outputIdentity]
    exact congrFun (d.mapped_output G P q core literal) x |>.trans
      (congrFun (eoRow_exact G P q core literal d).symm x)
  have binaryMapped (x : Fin 2 → Bool) : (original x : AlgebraicComplex)=f x := mapped _
  have originalPlane : Tensor.reindex e d.access.source.denote=EOBinaryPlaneCore.lift original := by
    funext x
    apply (ClosureSourceRows.embedding G).injective
    change (ClosureSourceRows.embedding G) (d.access.source.denote (fun j => x (e j)))=_
    rw [mapped]
    have h := congrFun plane x
    change EOBinaryPlaneCore.lift f x=M (fun j => x (e j)) at h
    rw [←h]
    unfold EOBinaryPlaneCore.lift
    split_ifs
    · exact (binaryMapped _).symm
    · exact (map_zero _).symm
  let c := F.scale (OI.K G) original
  have cn : c≠0 := F.scale_nonzero (OI.K G) original f binaryMapped full
  have power := F.power (OI.K G) original f binaryMapped full fa fp
  let D : GeneralEODEQProducerNormalize.Produced P.table :=
    ⟨A.network d.access.source e 23,
      A.labels d.access.source (S.labels G P q core literal d) e 23,
      A.exact d.access.source (S.labels G P q core literal d) e P.table
        (S.exact G P q core literal d) 23,
      A.native d.access.source e d.access.native 23,c,cn,
      A.power_denote d.access.source e original originalPlane 23 c power⟩
  exact ⟨GlobalCloseCompletionSparseEq4Flip.produce G P D⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionAffineAncestorEq4
end
