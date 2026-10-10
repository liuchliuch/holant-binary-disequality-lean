import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixDressing
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralPreparedSix

/-! The actual all-pair matching predicate is preserved by each independent
literal T leg and by every physical port permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.TetrahedralLocalization
open Holant.Platonic.StabilizerShortening
open Normalization

def AllPairs (f : Signature ℂ 6) : Prop :=
  ∀ p : Equiv.Perm (Fin 6), ∀ K : Matrix Bool Bool ℂ,
    groupDirection .tetrahedral K →
    matchingCone .tetrahedral (Signature.contract K (Tensor.reindex p f))

theorem contract_reindex (p : Equiv.Perm (Fin 6)) (K : Matrix Bool Bool ℂ)
    (f : Signature ℂ 6) :
    Signature.contract K (Tensor.reindex p f)=pairCard ((firstPair 4).trans p.symm) K f := by
  ext x
  have hw (a b : Bool) :
      (fun i : Fin 6 => (Fin.cons a (Fin.cons b x) : Fin 6 → Bool) (p i))=
        pairInsert ((firstPair 4).trans p.symm) a b x := by
    ext i
    change (Fin.cons a (Fin.cons b x) : Fin 6 → Bool) (p i)=
      pairInsert (firstPair 4) a b x (p i)
    rw [pairInsert_firstPair]
  simp only [Signature.contract,Tensor.reindex,pairCard,LinearMap.coe_mk,AddHom.coe_mk,hw]

theorem AllPairs.reindex {f : Signature ℂ 6} (hf : AllPairs f) (e : Equiv.Perm (Fin 6)) :
    AllPairs (Tensor.reindex e f) := by
  intro p K hK
  rw [Tensor.reindex_trans]
  exact hf _ K hK

theorem pairKernel_direction (A B K : Matrix Bool Bool ℂ)
    (hA : groupDirection .tetrahedral A) (hB : groupDirection .tetrahedral B)
    (hK : groupDirection .tetrahedral K) :
    groupDirection .tetrahedral (OctahedralSeparator.pairKernel A B K) := by
  have he : OctahedralSeparator.pairKernel A B K=A.transpose*(K*B) := rfl
  rw [he]
  exact groupDirection_mul .tetrahedral (groupDirection_transpose .tetrahedral hA)
    (groupDirection_mul .tetrahedral hK hB)

theorem AllPairs.coordinate_action {f : Signature ℂ 6} (hf : AllPairs f)
    (M : Fin 6 → Matrix Bool Bool ℂ) (hm : ∀j,groupDirection .tetrahedral (M j)) :
    AllPairs (Signature.coordinateAction M f) := by
  intro p K hK
  rw [OctahedralSeparator.reindex_action,OctahedralSeparator.contract_action]
  have hk := pairKernel_direction (M (p.symm 0)) (M (p.symm 1)) K
    (hm _) (hm _) hK
  exact action_matchingCone .tetrahedral (fun j => M (p.symm j.succ.succ))
    (fun j => hm _) _ (hf p _ hk)

theorem ofDomain_legs_mem (D : Holant.Platonic.RankDeficientLocalization.Normalization.DomainAction .tetrahedral)
    (L : Legs) (hL : GroupLegs .tetrahedral L) :
    ∀j,groupDirection .tetrahedral ((SixDressing.ofDomain D L).legs j) := by
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => hL k) j) j
  · exact groupDirection_transpose .tetrahedral D.left_mem
  · exact D.right_mem

theorem AllPairs.dressing {f : Signature ℂ 6} (hf : AllPairs f) (D : SixDressing)
    (hd : ∀j,groupDirection .tetrahedral (D.legs j)) : AllPairs (D.tensor f) :=
  (hf.coordinate_action D.legs hd).reindex D.portOrder

open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source

theorem actual_all_pairs {L : Type*} [Field L] [NumberField L]
    (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (literal : group phi F torsion=Holant.Projective.FiniteGroupFacts.modelPGL .tetrahedral)
    (f : Signature L 6) (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    AllPairs (RingHomRealization.mapSignature (complexEmbedding phi) f) := by
  intro p K hK
  rw [contract_reindex]
  exact GlobalCloseCompletionTetrahedralPreparedSix.pair_matching phi F torsion literal f stable _ K hK


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSix
end
