import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalOppositeThreePhase

/-! Exact lift along an affine Boolean embedding with a fixed affine section.
The support equations are constructed as the kernel of the actual retraction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXAffineEmbeddingLift
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.TwoTranslate
open Holant.ReedMuller.AffinePatching
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {r n : ℕ} (e : Word r→Word n) (p : Word n→Word r)
variable (he : IsAffineMap e) (hp : IsAffineMap p)
def difference (x : Word n) : Word n := xor x (e (p x))
include he hp in
theorem difference_affine : IsAffineMap (difference e p) := by
  have hc : IsAffineMap (fun x=>e (p x)) :=
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionGadget.affine_comp e p he hp
  intro x y
  have h := hc x y
  funext i
  have hi := congrFun h i
  change e (p (xor x y)) i=(e (p x) i ^^ (e (p y) i ^^ e (p (origin n)) i)) at hi
  change ((x i ^^ y i) ^^ e (p (xor x y)) i)=
    ((x i ^^ e (p x) i) ^^ ((y i ^^ e (p y) i) ^^ (false ^^ e (p (origin n)) i)))
  rw [hi]
  cases x i <;> cases y i <;> cases e (p x) i <;> cases e (p y) i <;>
    cases e (p (origin n)) i <;> rfl

def system : AffineSystem n := (originSystem n).pullback (difference e p)
include he hp in
theorem system_holds (x : Word n) : (system e p).Holds x ↔ x=e (p x) := by
  rw [system,AffineSystem.pullback_holds _ _ (difference_affine e p he hp),originSystem_holds]
  constructor
  · intro hx
    funext i
    have hi := congrFun hx i
    change (x i ^^ e (p x) i)=false at hi
    cases a : x i <;> cases b : e (p x) i <;> simp_all
  · intro hx
    change xor x (e (p x))=origin n
    rw [←hx]
    exact AffinePhase.xor_self x

def lift (h : Signature AlgebraicComplex r) : Signature AlgebraicComplex n :=
  fun x=>if x=e (p x) then h (p x) else 0
include he hp in
theorem affine_lift {h : Signature AlgebraicComplex r} (ha : Affine h) : Affine (lift e p h) := by
  have hA := (ha.precompose p hp).restrict (system e p)
  convert hA using 1
  funext x
  simp only [lift,system_holds e p he hp]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXAffineEmbeddingLift
end
