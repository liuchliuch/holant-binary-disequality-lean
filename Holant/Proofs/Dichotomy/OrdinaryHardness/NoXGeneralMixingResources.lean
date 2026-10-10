import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOppositeMixingSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOppositeUnaryMixing

/-! Actual resource forms selected separately from the three whole-family
class obstructions. The finite mixer consumes their original-table graphs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralMixingResources
open Holant Holant.Tractable
open OrdinaryNegativeXUniversalResource
namespace O
export NoXOppositeMixingLift (opposite)
end O
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val))

structure OppositeAlpha (kind : Kind) extends OddResource (s:=s) b (kind.arity+kind.arity) where
  alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action
    (fun x=>toOddResource.ambient H (O.opposite x)))
  full : ∀x,toOddResource.ambient H (O.opposite (kind.code x))≠0

structure OppositeAffine (kind : Kind) extends OddResource (s:=s) b (kind.arity+kind.arity) where
  affine : Affine (fun x=>toOddResource.ambient H (O.opposite x))
  full : ∀x,toOddResource.ambient H (O.opposite (kind.code x))≠0

structure FullUnary extends OddResource (s:=s) b 1 where
  full : ∀x,toOddResource.ambient H x≠0

def OrdinarySupply : Prop :=
  (∃kind,Nonempty (AlphaResource H kind)) ∨ (∃kind,Nonempty (OppositeAlpha H kind))
def UniformSupply : Prop :=
  (∃kind,Nonempty (AffineResource H kind)) ∨ (∃kind,Nonempty (OppositeAlpha H kind))
def LocalSupply : Prop :=
  Nonempty (FullUnary H) ∨ (∃kind,Nonempty (OppositeAffine H kind))

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

theorem opposite_evenBad (ka : Kind) (first : OppositeAlpha H ka) (localSupply : LocalSupply H) : EvenBad H := by
  rcases localSupply with unaryCase|⟨kb,⟨second⟩⟩
  · obtain ⟨u⟩ := unaryCase
    exact NoXOppositeUnaryMixing.evenBad (u.toOddResource.ambient H) ka
      (first.toOddResource.ambient H) first.alpha first.full H first.toOddResource u.toOddResource
      rfl rfl u.full
  · exact NoXOppositeMixingSource.evenBad H ka kb first.toOddResource second.toOddResource
      first.alpha second.affine first.full second.full

theorem evenBad (ordinary : OrdinarySupply H) (uniform : UniformSupply H)
    (localSupply : LocalSupply H) : EvenBad H := by
  rcases ordinary with ⟨ka,⟨first⟩⟩|⟨ka,⟨first⟩⟩
  · rcases uniform with ⟨kb,⟨second⟩⟩|⟨kb,⟨second⟩⟩
    · exact OrdinaryNegativeXUniversalMixing.evenBad_of_resources H ka kb first second
    · exact opposite_evenBad H kb second localSupply
  · exact opposite_evenBad H ka first localSupply

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralMixingResources
end
