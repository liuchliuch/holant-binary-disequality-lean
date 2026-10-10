import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixDressing
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicPreparedSix

/-! The actual all-pair matching predicate is preserved by each independent
literal Platonic leg and by every physical port permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicSix
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
open Holant.Platonic.TetrahedralLocalization
open Holant.Platonic.StabilizerShortening
open GlobalCloseCompletionTetrahedralSix.Normalization

def AllPairs (g : PlatonicModel) (f : Signature ℂ 6) : Prop :=
  ∀ p : Equiv.Perm (Fin 6), ∀ K : Matrix Bool Bool ℂ,
    groupDirection g K →
    matchingCone g (Signature.contract K (Tensor.reindex p f))

theorem AllPairs.prepared {g : PlatonicModel} {f : Signature ℂ 6} (hf : AllPairs g f) :
    ∀ i : Fin (size g), matchingCone g (actualMap f (representative g i)) := by
  intro i
  simpa only [Tensor.reindex_refl,actualMap_apply] using hf (Equiv.refl _) _ (representative_mem g i)

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

theorem AllPairs.reindex {g : PlatonicModel} {f : Signature ℂ 6} (hf : AllPairs g f) (e : Equiv.Perm (Fin 6)) :
    AllPairs g (Tensor.reindex e f) := by
  intro p K hK
  rw [Tensor.reindex_trans]
  exact hf _ K hK

theorem pairKernel_direction (g : PlatonicModel) (A B K : Matrix Bool Bool ℂ)
    (hA : groupDirection g A) (hB : groupDirection g B)
    (hK : groupDirection g K) :
    groupDirection g (OctahedralSeparator.pairKernel A B K) := by
  have he : OctahedralSeparator.pairKernel A B K=A.transpose*(K*B) := rfl
  rw [he]
  exact groupDirection_mul g (groupDirection_transpose g hA)
    (groupDirection_mul g hK hB)

theorem AllPairs.coordinate_action {g : PlatonicModel} {f : Signature ℂ 6} (hf : AllPairs g f)
    (M : Fin 6 → Matrix Bool Bool ℂ) (hm : ∀j,groupDirection g (M j)) :
    AllPairs g (Signature.coordinateAction M f) := by
  intro p K hK
  rw [OctahedralSeparator.reindex_action,OctahedralSeparator.contract_action]
  have hk := pairKernel_direction g (M (p.symm 0)) (M (p.symm 1)) K
    (hm _) (hm _) hK
  exact action_matchingCone g (fun j => M (p.symm j.succ.succ))
    (fun j => hm _) _ (hf p _ hk)

theorem ofDomain_legs_mem {g : PlatonicModel} (D : Holant.Platonic.RankDeficientLocalization.Normalization.DomainAction g)
    (L : Legs) (hL : GroupLegs g L) :
    ∀j,groupDirection g ((SixDressing.ofDomain D L).legs j) := by
  intro j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => hL k) j) j
  · exact groupDirection_transpose g D.left_mem
  · exact D.right_mem

theorem AllPairs.dressing {g : PlatonicModel} {f : Signature ℂ 6} (hf : AllPairs g f) (D : SixDressing)
    (hd : ∀j,groupDirection g (D.legs j)) : AllPairs g (D.tensor f) :=
  (hf.coordinate_action D.legs hd).reindex D.portOrder

open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source

theorem actual_all_pairs {L : Type*} [Field L] [NumberField L]
    (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (g : PlatonicModel)
    (literal : group phi F torsion=Holant.Projective.FiniteGroupFacts.modelPGL g)
    (f : Signature L 6) (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    AllPairs g (RingHomRealization.mapSignature (complexEmbedding phi) f) := by
  intro p K hK
  rw [contract_reindex]
  exact GlobalCloseCompletionPlatonicPreparedSix.pair_matching phi F torsion g literal f stable _ K hK


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicSix
end
