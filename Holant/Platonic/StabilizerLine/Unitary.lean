import Holant.Platonic.StabilizerLine.Program

/-! The actual standard Hermitian form is preserved by every analytic gate.
In particular the partial transform carries its genuine unitary normalization. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
open scoped ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n r s : ℕ}

def hermitian (f g : Signature ℂ n) : ℂ := ∑ x,conj (f x)*g x

def wordBlockEquiv (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) :
    Word n ≃ Word r×Word s where
  toFun x := (wordVector (e (vectorWord x)).1,wordVector (e (vectorWord x)).2)
  invFun p := wordVector (e.symm (vectorWord p.1,vectorWord p.2))
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem blockWalsh_at_block
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f : Signature ℂ n) (a : Word r) (b : Word s) :
    blockWalsh e f ((wordBlockEquiv e).symm (a,b))=
      ((sqrtTwo⁻¹^r:AlgebraicComplex):ℂ)*∑ t,(walshKernel a t:ℂ)*f ((wordBlockEquiv e).symm (t,b)) := by
  simp [blockWalsh,blockWord,wordBlockEquiv]

theorem hermitian_block (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f g : Signature ℂ n) : hermitian f g=
      ∑ b : Word s,∑ a : Word r,
        conj (f ((wordBlockEquiv e).symm (a,b)))*g ((wordBlockEquiv e).symm (a,b)) := by
  unfold hermitian
  rw [←(wordBlockEquiv e).symm.sum_comp,Fintype.sum_prod_type,Finset.sum_comm]

@[simp] theorem conj_walshKernel (x y : Word r) : conj (walshKernel x y:ℂ)=(walshKernel x y:ℂ) := by
  simp only [walshKernel]
  push_cast
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> cases y i <;> simp [hadamard]

theorem walshKernel_comm (x y : Word r) : walshKernel x y=walshKernel y x := by
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> cases y i <;> rfl

@[simp] theorem conj_sqrt_normalization (r : ℕ) :
    conj ((sqrtTwo⁻¹^r:AlgebraicComplex):ℂ)=((sqrtTwo⁻¹^r:AlgebraicComplex):ℂ) := by
  push_cast
  simp

theorem blockWalsh_selfAdjoint
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f g : Signature ℂ n) : hermitian (blockWalsh e f) g=hermitian f (blockWalsh e g) := by
  rw [hermitian_block e,hermitian_block e]
  simp only [blockWalsh_at_block,map_mul,map_sum,conj_sqrt_normalization,conj_walshKernel,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro t _
  rw [walshKernel_comm t a]
  ring

theorem blockWalsh_unitary
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f g : Signature ℂ n) : hermitian (blockWalsh e f) (blockWalsh e g)=hermitian f g := by
  rw [blockWalsh_selfAdjoint,blockWalsh_involution]

@[simp] theorem phase_norm (q : ZMod 4) :
    conj (fourthRootPhase q:ℂ)*(fourthRootPhase q:ℂ)=1 := by
  rcases Holant.Tractable.TwoTranslate.fourth_cases q with rfl|rfl|rfl|rfl <;>
    norm_num [Complex.I_sq]

theorem phaseAction_unitary (Q : QuadraticPhase n) (rev : Bool) (f g : Signature ℂ n) :
    hermitian (phaseAction Q rev f) (phaseAction Q rev g)=hermitian f g := by
  unfold hermitian phaseAction
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  calc
    _ = (conj (fourthRootPhase (phaseExponent Q rev x):ℂ)*
        (fourthRootPhase (phaseExponent Q rev x):ℂ))*(conj (f x)*g x) := by ring
    _ = _ := by rw [phase_norm,one_mul]

def translationEquiv (a : BinaryVector n) : Word n ≃ Word n where
  toFun x := wordVector (vectorWord x+a)
  invFun x := wordVector (vectorWord x+a)
  left_inv x := by simp [add_assoc,binary_self]
  right_inv x := by simp [add_assoc,binary_self]

theorem translateAction_unitary (a : BinaryVector n) (f g : Signature ℂ n) :
    hermitian (translateAction a f) (translateAction a g)=hermitian f g := by
  exact (translationEquiv a).sum_comp (fun x => conj (f x)*g x)

theorem Program.unitary (P : Program n) (f g : Signature ℂ n) :
    hermitian (P.run f) (P.run g)=hermitian f g := by
  induction P generalizing f g with
  | identity => rfl
  | phase Q rev => exact phaseAction_unitary Q rev f g
  | translate a => exact translateAction_unitary a f g
  | hadamard r s e => exact blockWalsh_unitary e f g
  | comp P Q ihP ihQ => exact (ihP _ _).trans (ihQ _ _)

end
end Holant.Platonic.StabilizerLine
