import Holant.Platonic.StabilizerLine.Normalized
import Holant.ReedMuller.AffinePatching.WalshInversion

/-! A normalized partial Hadamard in an explicitly supplied invertible binary
coordinate system. Its inverse and affine preservation are proved from the
literal finite sum, not postulated as a stabilizer operation. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.TwoChart
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n r s : ℕ}

def leftCoordinates (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) :
    BinaryVector n →ₗ[ZMod 2] BinaryVector r := (LinearMap.fst ..).comp e.toLinearMap

def rightCoordinates (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) :
    BinaryVector n →ₗ[ZMod 2] BinaryVector s := (LinearMap.snd ..).comp e.toLinearMap

def blockWord (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (t : Word r) (x : Word n) : Word n :=
  wordVector (e.symm (vectorWord t,(e (vectorWord x)).2))

def blockWalshAlg (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex n := fun x =>
  sqrtTwo⁻¹^r*∑ t : Word r,walshKernel (wordVector ((e (vectorWord x)).1)) t*f (blockWord e t x)

def blockWalsh (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f : Signature ℂ n) : Signature ℂ n := fun x =>
  (sqrtTwo⁻¹^r:AlgebraicComplex)*∑ t : Word r,
    (walshKernel (wordVector ((e (vectorWord x)).1)) t:ℂ)*f (blockWord e t x)

def prefixLinear (m k : ℕ) : BinaryVector (m+k) →ₗ[ZMod 2] BinaryVector k :=
  LinearMap.pi fun i => LinearMap.proj (prefixPort m k i)

def suffixLinear (m k : ℕ) : BinaryVector (m+k) →ₗ[ZMod 2] BinaryVector m :=
  LinearMap.pi fun i => LinearMap.proj (suffixPort m k i)

def blockInput (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s) :
    BinaryVector (n+r) →ₗ[ZMod 2] BinaryVector n :=
  e.symm.toLinearMap.comp ((prefixLinear n r).prod
    ((rightCoordinates e).comp (suffixLinear n r)))

theorem hadamard_phase (a b : Bool) :
    hadamard a b=fourthRootPhase (evenLift (bitValue (ZMod 2) a*bitValue (ZMod 2) b)) := by
  cases a <;> cases b <;> norm_num [hadamard,bitValue]

def blockJoint (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex (n+r) := fun z =>
  (∏ i : Fin r,fourthRootPhase (evenLift
    (leftCoordinates e (suffixLinear n r (vectorWord z)) i*prefixLinear n r (vectorWord z) i)))*
    f (affineBoolean 0 (blockInput e) z)

theorem blockJoint_affine (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f : Signature AlgebraicComplex n) (hf : Affine f) : Affine (blockJoint e f) := by
  apply Affine.mul
  · apply affine_finset_prod Finset.univ
    intro i _
    exact affine_bilinear_sign
      ((LinearMap.proj i).comp ((leftCoordinates e).comp (suffixLinear n r)))
      ((LinearMap.proj i).comp (prefixLinear n r))
  · exact hf.precompose _ (affineBoolean_isAffine 0 (blockInput e))

theorem prefix_insert (x : Word n) (t : Word r) :
    prefixLinear n r (vectorWord (insertWord n r t x))=vectorWord t := by
  ext i
  simp only [prefixLinear,LinearMap.pi_apply,LinearMap.proj_apply,vectorWord,insertWord_prefix]

theorem suffix_insert (x : Word n) (t : Word r) :
    suffixLinear n r (vectorWord (insertWord n r t x))=vectorWord x := by
  ext i
  simp only [suffixLinear,LinearMap.pi_apply,LinearMap.proj_apply,vectorWord,insertWord_suffix]

theorem blockJoint_insert (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f : Signature AlgebraicComplex n) (t : Word r) (x : Word n) :
    blockJoint e f (insertWord n r t x)=
      walshKernel (wordVector ((e (vectorWord x)).1)) t*f (blockWord e t x) := by
  have hv (y : BinaryVector r) (i : Fin r) : bitValue (ZMod 2) (wordVector y i)=y i :=
    boolEquiv.apply_symm_apply _
  simp only [blockJoint,affineBoolean,zero_add,blockInput,LinearMap.comp_apply,
    LinearMap.prod_apply,Function.prod_apply,prefix_insert,suffix_insert,leftCoordinates,rightCoordinates,
    LinearMap.fst_apply,LinearMap.snd_apply,LinearEquiv.coe_coe,blockWord,walshKernel,hadamard_phase,hv]
  rfl

theorem blockWalshAlg_affine (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f : Signature AlgebraicComplex n) (hf : Affine f) : Affine (blockWalshAlg e f) := by
  have h := (sumVariables_affine n r _ (blockJoint_affine e f hf)).scale (sqrtTwo⁻¹^r)
  convert h using 1
  funext x
  simp only [blockWalshAlg,sumVariables_eq,blockJoint_insert]

theorem blockWalsh_affine (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r×BinaryVector s)
    (f : Signature ℂ n) (hf : ComplexAffine f) : ComplexAffine (blockWalsh e f) := by
  obtain ⟨c,g,hg,he⟩ := hf
  refine ⟨c,blockWalshAlg e g,blockWalshAlg_affine e g hg,?_⟩
  intro x
  simp only [blockWalsh,blockWalshAlg,he]
  push_cast
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

end
end Holant.Platonic.StabilizerLine
