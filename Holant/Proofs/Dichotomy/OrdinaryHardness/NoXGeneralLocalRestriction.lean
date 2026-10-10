import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSinglePairStar
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralUniformTranslation
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOriginRestrictionSupport

/-! A genuine bad LocalAffine row has a lower-rank literal pin or equality
restriction. The equality pair has equal bits at the supported bad marker;
only semantic coordinate translation is used in the full-support criterion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRestriction
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
namespace T
export NoXReciprocalMixedProjectionCore (logical)
export NoXGeneralUniformTranslation (affine_map involution)
end T
namespace S
export NoXLocalStarCriterion (zeroCut equalCut)
export NoXLocalPairSupport (equalMask)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
section Semantic
variable {n r : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)

def shifted (a : Word r) : Word r→Word n := fun x=>D.encode (T.logical a x)
def phase (a : Word r) : Signature AlgebraicComplex r :=
  fun x=>localTwist (D.encode a) f (shifted D a x)

theorem shifted_affine (a : Word r) : TwoTranslate.IsAffineMap (shifted D a) :=
  affine_map_comp D.encode (T.logical a) D.affine (T.affine_map a)

theorem phase_full (a x : Word r) : phase D a x≠0 :=
  (NoXLocalRankOneCriterion.twist_support f (D.encode a) _).mpr (D.supported _)

theorem bad_phase (square : Affine (fun x=>f x^2)) (bad : ¬LocalAffine f) :
    ∃a : Word r,¬Affine (phase D a) := by
  obtain ⟨a,z,i,j,k,cube⟩:=NoXLocalAffineCubeWitness.witness D square bad
  refine ⟨a,?_⟩
  intro good
  have actual:=good.precompose (T.logical a) (T.affine_map a)
  have exactPhase : (fun x=>phase D a (T.logical a x))=
      (fun x=>localTwist (D.encode a) f (D.encode x)) := by
    funext x
    simp only [phase,shifted,T.involution]
  rw [exactPhase] at actual
  exact cube (thirdTrivial_of_affine (fun x=>(NoXLocalRankOneCriterion.twist_support f (D.encode a) _).mpr
    (D.supported x)) actual z (basis i) (basis j) (basis k))

theorem same_pair (higher : 3≤r) (a : Word r) : ∃p q : Fin r,p≠q ∧ a p=a q := by
  have not_injective : ¬Function.Injective a := by
    intro inj
    have bound:=Fintype.card_le_of_injective a inj
    simp only [Fintype.card_fin,Fintype.card_bool] at bound
    omega
  obtain ⟨p,q,equal,ne⟩:=Function.not_injective_iff.mp not_injective
  exact ⟨p,q,ne,equal⟩

theorem pin_twist (a : Word n) (p : Fin n) (bit : Bool) :
    localTwist a (pinMask f p bit)=pinMask (localTwist a f) p bit := by
  funext x
  by_cases hx : x p=bit <;> simp [localTwist_apply,pinMask,hx]

theorem equal_twist (a : Word n) (p q : Fin n) :
    localTwist a (S.equalMask f p q)=S.equalMask (localTwist a f) p q := by
  funext x
  by_cases hx : x p=x q <;> simp [localTwist_apply,S.equalMask,hx]

theorem pin_phase (a : Word r) (i : Fin r)
    (good : LocalAffine (pinMask f (D.ports i) (a i))) : Affine (S.zeroCut (phase D a) i) := by
  have ha:=good (D.encode a) (by simpa only [pinMask,D.free,ite_true] using D.supported a)
  rw [pin_twist] at ha
  have pulled:=ha.precompose (shifted D a) (shifted_affine D a)
  convert pulled using 1
  funext x
  simp only [S.zeroCut,phase,pinMask,shifted,D.free,T.logical]
  cases a i <;> cases x i <;> rfl

theorem equal_phase (a : Word r) (i j : Fin r) (same : a i=a j)
    (good : LocalAffine (S.equalMask f (D.ports i) (D.ports j))) :
    Affine (S.equalCut (phase D a) i j) := by
  have ha:=good (D.encode a) (by simpa only [S.equalMask,D.free,ite_eq_left same] using D.supported a)
  rw [equal_twist] at ha
  have pulled:=ha.precompose (shifted D a) (shifted_affine D a)
  convert pulled using 1
  funext x
  simp only [S.equalCut,phase,S.equalMask,shifted,D.free,T.logical,same]
  cases a j <;> cases x i <;> cases x j <;> rfl

end Semantic

section Descent
variable {n t : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f (t+4))
include D in
theorem restriction (square : Affine (fun x=>f x^2)) (bad : ¬LocalAffine f) :
    (∃p : Fin n,∃bit : Bool,¬LocalAffine (pinMask f p bit) ∧
      Nonempty (SystematicSupport (pinMask f p bit) (t+3))) ∨
    (∃p q : Fin n,p≠q ∧ ¬LocalAffine (S.equalMask f p q) ∧
      Nonempty (SystematicSupport (S.equalMask f p q) (t+3))) := by
  obtain ⟨a,ha⟩:=bad_phase D square bad
  obtain ⟨p,q,pq,same⟩:=same_pair (by omega : 3≤t+4) a
  rcases NoXGeneralSinglePairStar.bad_cut (phase D a) (phase_full D a) p q pq (by omega) ha with pin|pair
  · obtain ⟨i,hi⟩:=pin
    exact Or.inl ⟨D.ports i,a i,(fun good=>hi (pin_phase D a i good)),
      NoXOriginRestrictionSupport.pin_chart D i (a i)⟩
  · exact Or.inr ⟨D.ports p,D.ports q,(fun eqn=>pq (D.injective eqn)),
      (fun good=>pair (equal_phase D a p q same good)),NoXOriginRestrictionSupport.equal_chart D p q pq⟩
end Descent

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRestriction
end
