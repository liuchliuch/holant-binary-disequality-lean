import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicHigherCards
import Holant.Platonic.RainbowLocalization.PhysicalCards
import Holant.Platonic.TetrahedralLocalization.Reconstruction

/-! All actual original pairs, including their exact surviving port names,
are supplied by the complete raw deck. The only finite reindexing is the
bijection between the original residual ports and their Fin enumeration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicNamedCards
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.TetrahedralLocalization
open Holant.Platonic.StabilizerShortening
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open GlobalCloseCompletionPlatonicHigherCards
open scoped BigOperators

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (g : PlatonicModel)
variable (literal : group phi F torsion=Holant.Projective.FiniteGroupFacts.modelPGL g)

include literal in
theorem cardMap_matching {m : ℕ} {P : Type*} [Fintype P] [DecidableEq P]
    (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (p : Bool ⊕ P ≃ Fin (m+2)) (K : Matrix Bool Bool ℂ) (hk : groupDirection g K) :
    MatchingOrZero (directions g)
      (cardMap p (RingHomRealization.mapSignature (complexEmbedding phi) f) K) := by
  classical
  have hc : Fintype.card P=m := by
    have h := Fintype.card_congr p
    simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at h
    omega
  let e : Fin m ≃ P := (Fintype.equivFinOfCardEq hc).symm
  let p' : Bool ⊕ Fin m ≃ Fin (m+2) := (Equiv.sumCongr (Equiv.refl Bool) e).trans p
  let order : Equiv.Perm (Fin (m+2)) := p'.symm.trans (firstPair m)
  have h := ordered_card phi F torsion g literal f stable order K hk
  have he : cardMap p (RingHomRealization.mapSignature (complexEmbedding phi) f) K=
      Tensor.reindex e (Signature.contract K (Tensor.reindex order
        (RingHomRealization.mapSignature (complexEmbedding phi) f))) := by
    ext x
    have hw (a b : Bool) :
        pairAssignment p a b x=(fun i : Fin (m+2) =>
          (Fin.cons a (Fin.cons b (fun j => x (e j))) : Fin (m+2) → Bool) (order i)) := by
      ext i
      obtain ⟨j,rfl⟩ := p.surjective i
      cases j with
      | inl t => cases t <;> simp [pairAssignment,order,p',firstPair]
      | inr j => simp [pairAssignment,order,p',firstPair]
    simp only [cardMap,LinearMap.coe_mk,AddHom.coe_mk,Signature.contract,Tensor.reindex,hw]
  rw [he]
  exact h.reindex e

def pairPorts {n : ℕ} (u v : Fin n) (huv : u≠v) : Bool ⊕ Remaining u v ≃ Fin n where
  toFun := Sum.elim (fun b => if b then v else u) Subtype.val
  invFun i := if hu : i=u then .inl false else if hv : i=v then .inl true else .inr ⟨i,hu,hv⟩
  left_inv := by
    intro x
    cases x with
    | inl b => cases b <;> simp [huv,Ne.symm huv]
    | inr j => simp [j.property.1,j.property.2]
  right_inv := by
    intro i
    dsimp only
    split_ifs with hu hv
    · exact hu.symm
    · exact hv.symm
    · rfl

include literal in
theorem every_named_pair {m : ℕ} (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (u v : Fin (m+2)) (huv : u≠v) (K : Matrix Bool Bool ℂ) (hk : groupDirection g K) :
    MatchingOrZero (directions g)
      (contractPair u v K (RingHomRealization.mapSignature (complexEmbedding phi) f)) := by
  classical
  let p := pairPorts u v huv
  have h := cardMap_matching phi F torsion g literal f stable p K hk
  rw [cardMap_eq_contractPair] at h
  have hr := h.reindex (pairRemaining p)
  simpa [Tensor.reindex_trans,p,pairPorts] using hr


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicNamedCards
end
