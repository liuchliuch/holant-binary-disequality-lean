import Holant.Platonic.StabilizerLine.BlockWalsh

/-! Exact inversion and constant-fibre evaluation of the normalized block
Hadamard. The normalization is the literal positive square root of two. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n r s : ℕ}

def complexWalsh (f : Signature ℂ r) : Signature ℂ r := fun x =>
  ∑ y,(walshKernel x y:ℂ)*f y

theorem complexWalsh_inversion (f : Signature ℂ r) :
    complexWalsh (complexWalsh f)=fun x => (2:ℂ)^r*f x := by
  funext x
  unfold complexWalsh
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ z,∑ y,(walshKernel x y:ℂ)*((walshKernel y z:ℂ)*f z))=
        ∑ z,((∑ y,walshKernel x y*walshKernel y z:AlgebraicComplex):ℂ)*f z := by
      push_cast
      simp only [Finset.sum_mul,mul_assoc]
    _ = ∑ z,(if x=z then (2:ℂ)^r else 0)*f z := by
      simp only [walshKernel_orthogonal]
      simp only [apply_ite]
      push_cast
      rfl
    _ = (2:ℂ)^r*f x := by simp [ite_mul]

theorem complexWalsh_scale (f : Signature ℂ r) (c : ℂ) :
    complexWalsh (fun x => c*f x)=fun x => c*complexWalsh f x := by
  funext x
  simp only [complexWalsh,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

@[simp] theorem blockWord_coordinates
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) (t : Word r) (x : Word n) :
    e (vectorWord (blockWord e t x))=(vectorWord t,(e (vectorWord x)).2) := by
  simp [blockWord]

@[simp] theorem blockWord_blockWord
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) (t u : Word r) (x : Word n) :
    blockWord e t (blockWord e u x)=blockWord e t x := by
  simp [blockWord]

@[simp] theorem blockWord_self
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) (x : Word n) :
    blockWord e (wordVector ((e (vectorWord x)).1)) x=x := by
  simp [blockWord]

theorem sqrt_normalization (r : ℕ) : ((sqrtTwo⁻¹^r:AlgebraicComplex):ℂ)^2*(2:ℂ)^r=1 := by
  have h : (sqrtTwo⁻¹^r)^2*(2:AlgebraicComplex)^r=1 := by
    rw [pow_right_comm,inv_pow,sqrtTwo_sq,←mul_pow,inv_mul_cancel₀ (by norm_num),one_pow]
  have hh := congrArg (fun a : AlgebraicComplex => (a:ℂ)) h
  push_cast at hh
  exact hh

theorem blockWalsh_involution
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) (f : Signature ℂ n) :
    blockWalsh e (blockWalsh e f)=f := by
  funext x
  let F : Signature ℂ r := fun t => f (blockWord e t x)
  have h : blockWalsh e (blockWalsh e f) x=
      ((sqrtTwo⁻¹^r:AlgebraicComplex):ℂ)^2*
        complexWalsh (complexWalsh F) (wordVector ((e (vectorWord x)).1)) := by
    simp only [blockWalsh,blockWord_coordinates,word_vector,blockWord_blockWord,
      complexWalsh,F,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [h,complexWalsh_inversion]
  dsimp only
  rw [←mul_assoc,sqrt_normalization,one_mul]
  exact congrArg f (blockWord_self e x)

theorem blockWalsh_injective
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) :
    Function.Injective (blockWalsh e) := by
  intro f g h
  have hh := congrArg (blockWalsh e) h
  simpa only [blockWalsh_involution] using hh

theorem walshKernel_sum (x : Word r) :
    (∑ t : Word r,walshKernel x t)=if x=origin r then (2:AlgebraicComplex)^r else 0 := by
  have h := walshKernel_orthogonal x (origin r)
  simpa [walshKernel,hadamard,origin] using h

end
end Holant.Platonic.StabilizerLine
