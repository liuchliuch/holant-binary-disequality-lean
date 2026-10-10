import Holant.Platonic.StabilizerLine.Coordinates

/-! Concrete analytic gate syntax. No change of basis is treated as an
available physical gadget. The program stores only explicit binary coordinate
isomorphisms, source quadratic phases, translations and normalized Hadamards. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def phaseExponent (Q : QuadraticPhase n) (rev : Bool) (x : Word n) : ZMod 4 :=
  if rev then -Q.eval x else Q.eval x

def phaseAction (Q : QuadraticPhase n) (rev : Bool) (f : Signature ℂ n) : Signature ℂ n :=
  fun x => (fourthRootPhase (phaseExponent Q rev x):ℂ)*f x

def translateAction (a : BinaryVector n) (f : Signature ℂ n) : Signature ℂ n :=
  fun x => f (wordVector (vectorWord x+a))

theorem phaseAction_affine (Q : QuadraticPhase n) (rev : Bool)
    (f : Signature ℂ n) (hf : ComplexAffine f) : ComplexAffine (phaseAction Q rev f) := by
  obtain ⟨c,g,hg,he⟩ := hf
  have hp : Affine (fun x => fourthRootPhase (phaseExponent Q rev x)) := by
    apply affine_phase_of_thirdDifference
    intro z u v w
    cases rev
    · exact quadratic_thirdDifference Q z u v w
    · change thirdDifference (fun x => -Q.eval x) z u v w=0
      have h := thirdDifference_mul_const (-1) Q.eval z u v w
      simpa only [neg_one_mul,quadratic_thirdDifference,mul_zero] using h
  refine ⟨c,fun x => fourthRootPhase (phaseExponent Q rev x)*g x,hp.mul hg,?_⟩
  intro x
  dsimp [phaseAction]
  rw [he]
  push_cast
  ring

theorem translateAction_affine (a : BinaryVector n) (f : Signature ℂ n)
    (hf : ComplexAffine f) : ComplexAffine (translateAction a f) := by
  obtain ⟨c,g,hg,he⟩ := hf
  refine ⟨c,fun x => g (affineBoolean a LinearMap.id x),
    hg.precompose _ (affineBoolean_isAffine _ _),?_⟩
  intro x
  simpa [translateAction,affineBoolean,add_comm] using he (wordVector (vectorWord x+a))

theorem phaseAction_injective (Q : QuadraticPhase n) (rev : Bool) :
    Function.Injective (phaseAction Q rev) := by
  intro f g h
  funext x
  have hh := congrFun h x
  exact mul_left_cancel₀ (show (fourthRootPhase (phaseExponent Q rev x):ℂ)≠0 by
    exact_mod_cast fourthRootPhase_ne_zero _) hh

theorem translateAction_involution (a : BinaryVector n) (f : Signature ℂ n) :
    translateAction a (translateAction a f)=f := by
  funext x
  simp [translateAction,add_assoc,binary_self]

theorem translateAction_injective (a : BinaryVector n) : Function.Injective (translateAction a) := by
  intro f g h
  have hh := congrArg (translateAction a) h
  simpa only [translateAction_involution] using hh

inductive Program (n : ℕ) where
  | identity
  | phase (Q : QuadraticPhase n) (rev : Bool)
  | translate (a : BinaryVector n)
  | hadamard (r s : ℕ) (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
  | comp (P Q : Program n)

def Program.run : Program n → Signature ℂ n → Signature ℂ n
  | .identity,f => f
  | .phase Q rev,f => phaseAction Q rev f
  | .translate a,f => translateAction a f
  | .hadamard _ _ e,f => blockWalsh e f
  | .comp P Q,f => P.run (Q.run f)

theorem Program.affine (P : Program n) (f : Signature ℂ n) (hf : ComplexAffine f) :
    ComplexAffine (P.run f) := by
  induction P generalizing f with
  | identity => exact hf
  | phase Q rev => exact phaseAction_affine Q rev f hf
  | translate a => exact translateAction_affine a f hf
  | hadamard r s e => exact blockWalsh_affine e f hf
  | comp P Q ihP ihQ => exact ihP _ (ihQ _ hf)

theorem Program.injective (P : Program n) : Function.Injective P.run := by
  induction P with
  | identity => exact Function.injective_id
  | phase Q rev => exact phaseAction_injective Q rev
  | translate a => exact translateAction_injective a
  | hadamard r s e => exact blockWalsh_injective e
  | comp P Q ihP ihQ => exact ihP.comp ihQ

theorem Program.linear (P : Program n) (f g : Signature ℂ n) (a b : ℂ) :
    P.run (fun x => a*f x+b*g x)=fun x => a*P.run f x+b*P.run g x := by
  induction P generalizing f g with
  | identity => rfl
  | phase Q rev => funext x;dsimp [Program.run,phaseAction];ring
  | translate c => rfl
  | hadamard r s e =>
    funext x
    simp only [Program.run,blockWalsh,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> ring
  | comp P Q ihP ihQ =>
    simp only [Program.run,ihQ,ihP]

@[simp] theorem Program.zero (P : Program n) : P.run 0=0 := by
  have h := P.linear 0 0 0 0
  change P.run (fun _ => 0)=(fun _ => 0)
  simpa only [zero_mul,zero_add] using h

theorem Program.nonzero (P : Program n) (f : Signature ℂ n) (hf : f≠0) : P.run f≠0 := by
  intro h
  exact hf (P.injective (h.trans P.zero.symm))

end
end Holant.Platonic.StabilizerLine
