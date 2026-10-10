import Holant.Platonic.StabilizerLine.BlockPauli

/-! The source's genuine unitary Pauli-normalizer interface. The inverse is
explicit and preserves the literal fourth-root Pauli group in both directions.
Exterior amplitude normalization is not included in a Clifford operator. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def Program.inverse : Program n → Program n
  | .identity => .identity
  | .phase Q rev => .phase Q (!rev)
  | .translate a => .translate a
  | .hadamard r s e => .hadamard r s e
  | .comp P Q => .comp Q.inverse P.inverse

@[simp] theorem Program.inverse_inverse (P : Program n) : P.inverse.inverse=P := by
  induction P <;> simp [Program.inverse, *]

theorem phaseAction_inverse (Q : QuadraticPhase n) (rev : Bool) (f : Signature ℂ n) :
    phaseAction Q (!rev) (phaseAction Q rev f)=f := by
  funext x
  cases rev <;>
    simp [phaseAction,phaseExponent,fourthRootPhase_neg,←mul_assoc,
      show (fourthRootPhase (Q.eval x):ℂ)≠0 by exact_mod_cast fourthRootPhase_ne_zero _]

@[simp] theorem Program.inverse_run (P : Program n) (f : Signature ℂ n) :
    P.inverse.run (P.run f)=f := by
  induction P generalizing f with
  | identity => rfl
  | phase Q rev => exact phaseAction_inverse Q rev f
  | translate a => exact translateAction_involution a f
  | hadamard r s e => exact blockWalsh_involution e f
  | comp P Q ihP ihQ => simp only [Program.inverse,Program.run,ihP,ihQ]

@[simp] theorem Program.run_inverse (P : Program n) (f : Signature ℂ n) :
    P.run (P.inverse.run f)=f := by
  have h := P.inverse.inverse_run f
  simpa using h

theorem Program.normalizesPauli (P : Program n) : NormalizesPauli P.run := by
  induction P with
  | identity => exact fun A => ⟨A,fun _ => rfl⟩
  | phase Q rev => exact phaseAction_normalizes Q rev
  | translate a => exact translateAction_normalizes a
  | hadamard r s e => exact blockWalsh_normalizes e
  | comp P Q ihP ihQ =>
    intro A
    obtain ⟨B,hB⟩ := ihQ A
    obtain ⟨C,hC⟩ := ihP B
    refine ⟨C,?_⟩
    intro f
    simp only [Program.run,hB,hC]

def Program.linearEquiv (P : Program n) : Signature ℂ n ≃ₗ[ℂ] Signature ℂ n where
  toFun := P.run
  invFun := P.inverse.run
  left_inv := P.inverse_run
  right_inv := P.run_inverse
  map_add' := by
    intro f g
    change P.run (fun x => f x+g x)=(fun x => P.run f x+P.run g x)
    have h := P.linear f g 1 1
    simpa only [one_mul] using h
  map_smul' := by
    intro c f
    change P.run (fun x => c*f x)=(fun x => c*P.run f x)
    have h := P.linear f 0 c 0
    simpa only [zero_mul,add_zero] using h

/-- Standard finite-dimensional unitarity plus equality of the actual Pauli
normalizer: both forward and inverse conjugation preserve the exact group. -/
structure AnalyticClifford (n : ℕ) where
  operator : Signature ℂ n ≃ₗ[ℂ] Signature ℂ n
  unitary : ∀ f g,hermitian (operator f) (operator g)=hermitian f g
  pauli_forward : NormalizesPauli operator
  pauli_inverse : NormalizesPauli operator.symm

def Program.clifford (P : Program n) : AnalyticClifford n where
  operator := P.linearEquiv
  unitary := P.unitary
  pauli_forward := P.normalizesPauli
  pauli_inverse := P.inverse.normalizesPauli

@[simp] theorem Program.clifford_apply (P : Program n) (f : Signature ℂ n) :
    P.clifford.operator f=P.run f := rfl

/-- Its stored inverse is the actual Hermitian adjoint. -/
theorem AnalyticClifford.adjoint_identity (C : AnalyticClifford n)
    (f g : Signature ℂ n) :
    hermitian (C.operator f) g=hermitian f (C.operator.symm g) := by
  simpa using C.unitary f (C.operator.symm g)

/-- Literal conjugation, rather than only membership of transformed states. -/
theorem AnalyticClifford.conjugates (C : AnalyticClifford n) (P : Pauli n) :
    ∃ Q : Pauli n,∀ f,C.operator (P.run (C.operator.symm f))=Q.run f := by
  obtain ⟨Q,hQ⟩ := C.pauli_forward P
  exact ⟨Q,fun f => by rw [hQ,LinearEquiv.apply_symm_apply]⟩

theorem AnalyticClifford.inverse_conjugates (C : AnalyticClifford n) (P : Pauli n) :
    ∃ Q : Pauli n,∀ f,C.operator.symm (P.run (C.operator f))=Q.run f := by
  obtain ⟨Q,hQ⟩ := C.pauli_inverse P
  exact ⟨Q,fun f => by rw [hQ,LinearEquiv.symm_apply_apply]⟩

end
end Holant.Platonic.StabilizerLine
