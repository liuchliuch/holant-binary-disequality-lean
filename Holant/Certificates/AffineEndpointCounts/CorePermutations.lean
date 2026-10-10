import Holant.Certificates.AffineEndpointCounts.ProjectiveInputs
import Holant.Certificates.AffineEndpoint.CoreAffine
import Holant.Certificates.AffineEndpoint.OutputComplement
import Holant.ReedMuller.AffinePatching.WalshInversion

/-! Genuine affine-class permutations used in the source per-core counts.
The Walsh inverse has its actual factor 16, and every phase normalization
is carried by the projective permutation rather than discarded. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Certificates.AffineEndpoint Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace ProjectiveAffineAutomorphism

def comp (T U : ProjectiveAffineAutomorphism) : ProjectiveAffineAutomorphism where
  forward := T.forward.comp U.forward
  backward := U.backward.comp T.backward
  backward_forward := by
    obtain ⟨a,ha,hT⟩ := T.backward_forward
    obtain ⟨b,hb,hU⟩ := U.backward_forward
    refine ⟨a*b,mul_ne_zero ha hb,?_⟩
    intro f
    change U.backward.toFun (T.backward.toFun (T.forward.toFun (U.forward.toFun f))) = _
    rw [hT,U.backward.scale,hU,smul_smul]
  forward_backward := by
    obtain ⟨a,ha,hT⟩ := T.forward_backward
    obtain ⟨b,hb,hU⟩ := U.forward_backward
    refine ⟨b*a,mul_ne_zero hb ha,?_⟩
    intro f
    change T.forward.toFun (U.forward.toFun (U.backward.toFun (T.backward.toFun f))) = _
    rw [hU,T.forward.scale,hT,smul_smul]

end ProjectiveAffineAutomorphism

def phaseMap (j : Fin 4) : ProjectiveAffineMap where
  toFun := phaseTwist j
  scale := by intro a f; funext x; simp only [phaseTwist,Pi.smul_apply,smul_eq_mul]; ring
  affine := fun _ => phaseTwist_affine j
  nonzero := fun _ => phaseTwist_ne_zero j

def oppositePhase (j : Fin 4) : Fin 4 := ![0,3,2,1] j

theorem oppositePhase_root (j : Fin 4) :
    imaginaryUnit^(oppositePhase j).val * imaginaryUnit^j.val = 1 := by
  fin_cases j <;> norm_num [oppositePhase,imaginaryUnit_pow_three,←pow_two]

theorem phaseTwist_inverse (j : Fin 4) (f : Sig) :
    phaseTwist (oppositePhase j) (phaseTwist j f) = f := by
  funext x
  simp only [phaseTwist,←mul_assoc,←mul_pow,oppositePhase_root,one_pow,one_mul]

theorem oppositePhase_inverse : ∀j,oppositePhase (oppositePhase j)=j := by decide +kernel

def phaseAutomorphism (j : Fin 4) : ProjectiveAffineAutomorphism where
  forward := phaseMap j
  backward := phaseMap (oppositePhase j)
  backward_forward := ⟨1,one_ne_zero,fun f => by simpa only [phaseMap,one_smul] using phaseTwist_inverse j f⟩
  forward_backward := ⟨1,one_ne_zero,fun f => by
    simpa only [phaseMap,oppositePhase_inverse,one_smul] using phaseTwist_inverse (oppositePhase j) f⟩

def flipMap : ProjectiveAffineMap where
  toFun := fun f x => f (complementWord x)
  scale := by intros; rfl
  affine := fun f hf => hf.precompose _ complement_isAffineMap
  nonzero := by
    intro f hf hz
    apply hf
    funext x
    have h := congrFun hz (complementWord x)
    simpa only [complementWord_involutive,Pi.zero_apply] using h

def flipAutomorphism : ProjectiveAffineAutomorphism where
  forward := flipMap
  backward := flipMap
  backward_forward := ⟨1,one_ne_zero,fun f => by funext x; simp [flipMap]⟩
  forward_backward := ⟨1,one_ne_zero,fun f => by funext x; simp [flipMap]⟩

theorem walsh_zero : walsh (0 : Sig) = 0 := by
  funext x
  simp [walsh]

def walshMap : ProjectiveAffineMap where
  toFun := walsh
  scale := by
    intro a f
    rw [←coreAction_hadamard_zero,←coreAction_hadamard_zero]
    exact coordinateAction_scale _ a f
  affine := walsh_affine
  nonzero := by
    intro f hf hz
    have hh := walsh_inversion f
    rw [hz,walsh_zero] at hh
    apply hf
    funext x
    have hx := congrFun hh x
    have h16 : (2:AlgebraicComplex)^4 ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp hx.symm).resolve_left h16

def walshAutomorphism : ProjectiveAffineAutomorphism where
  forward := walshMap
  backward := walshMap
  backward_forward := ⟨2^4,pow_ne_zero _ (by norm_num),fun f => walsh_inversion f⟩
  forward_backward := ⟨2^4,pow_ne_zero _ (by norm_num),fun f => walsh_inversion f⟩

def evenHadamardAutomorphism (j : Fin 4) : ProjectiveAffineAutomorphism :=
  walshAutomorphism.comp (phaseAutomorphism j)

theorem evenHadamard_forward (j : Fin 4) (f : Sig) :
    (evenHadamardAutomorphism j).forward.toFun f =
      coreAction (.inr (.inl ⟨2*j.val,by omega⟩)) f := by
  rw [coreAction_hadamard_even,coreAction_hadamard_zero]
  rfl

end
end Holant.Certificates.AffineEndpointCounts
