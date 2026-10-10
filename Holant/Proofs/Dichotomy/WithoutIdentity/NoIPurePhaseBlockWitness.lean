import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseBlockTransform
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseSmallPorts

/-! Exact original-row blocks for semantic pure-pin support witnesses.
Pinned phase constants stay explicit, and the nonzero scalar is removed only
inside Affine class reflection. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseBlockWitness
open Holant Holant.Tractable
open NoIPurePhaseRecipeFactor (Port word)
open NoIPurePhaseBlock
namespace U
export NoIPureClosedUniformMinimal (twist twistChart UniformPinWitness)
end U
namespace P
export NoIPurePhasePinCompose (PurePins substitute compose fixedWeight)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {n l m d : ℕ}

theorem scalar_affine_iff (c : AlgebraicComplex) (cn : c≠0)
    (g : Signature AlgebraicComplex m) : Affine (fun z=>c*g z)↔Affine g := by
  constructor
  · intro h
    convert h.scale c⁻¹ using 1
    funext z
    rw [←mul_assoc,inv_mul_cancel₀ cn,one_mul]
  · exact fun h=>h.scale c

def pinBlock (pins : Fin n→Bool⊕Fin l) (p : Fin l→Port m) : Block n m :=
  pinLift pins (single p)

theorem pin_value {K : Type} [CommMonoid K] (f : Signature K n)
    (pins : Fin n→Bool⊕Fin l) (p : Fin l→Port m) (z : Fin m→Bool) :
    value f (pinBlock pins p) z=f (P.substitute pins (word p z)) := by
  rw [pinBlock,value_pinLift,value_single]

theorem pin_charge (pins : Fin n→Bool⊕Fin l) (pure : P.PurePins pins)
    (p : Fin l→Port m) (j : Fin m) :
    NoIPurePhaseBlock.charge (pinBlock pins p) j=NoIPurePhaseRecipeFactor.incidence p j := by
  rw [pinBlock,charge_pinLift pins pure,charge_single]

theorem pin_phase (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (pins : Fin n→Bool⊕Fin l) (pure : P.PurePins pins)
    (p : Fin l→Port m) (z : Fin m→Bool) :
    phase r f (pinBlock pins p) z=
      r^(P.fixedWeight pins)*U.twist r (fun x=>f (P.substitute pins x)) (word p z) := by
  rw [pinBlock,phase_pinLift r f pins pure,phase_single]
  simp only [single,pow_one]
  rfl

theorem pin_affine (r : AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (pins : Fin n→Bool⊕Fin l) (pure : P.PurePins pins) (p : Fin l→Port m)
    (good : Affine (U.twist r (fun x=>f (P.substitute pins x)))) :
    Affine (phase r f (pinBlock pins p)) := by
  have h:=(good.precompose (word p) (NoIPurePhaseAnchorRecipe.word_affine p)).scale
    (r^(P.fixedWeight pins))
  change Affine (fun z=>phase r f (pinBlock pins p) z)
  simpa only [pin_phase r f pins pure p] using h

theorem pin_bad (r : AlgebraicComplex) (rn : r≠0) (f : Signature AlgebraicComplex n)
    (pins : Fin n→Bool⊕Fin l) (pure : P.PurePins pins) (p : Fin l→Port m)
    (code : (Fin d→Bool)→(Fin m→Bool))
    (bad : ¬Affine (fun x=>U.twist r (fun z=>f (P.substitute pins z)) (word p (code x)))) :
    ¬Affine (fun x=>phase r f (pinBlock pins p) (code x)) := by
  intro h
  apply bad
  apply (scalar_affine_iff (r^(P.fixedWeight pins)) (pow_ne_zero _ rn) _).mp
  simpa only [pin_phase r f pins pure p] using h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseBlockWitness
end
