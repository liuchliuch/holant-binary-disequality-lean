import Holant.Platonic.StabilizerErasure.PhysicalTensorFrames
import Holant.Certificates.TetrahedralAffine.Binaries

/-! Literal tetrahedral kernels selected in the finite physical axis frames
constructed in Lemma 9.20. The inverse frames are analytic coordinates only;
the contracted matrix is one of the fixed twelve actual representatives. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.TetrahedralAffine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The inverse axis frame with its positive Hadamard normalization removed. -/
def inverseAxisRaw : Fin 4 → Kernel ℂ
  | 0 => Signature.equality
  | 1 => fun a b => if a && b then -1 else 1
  | 2 => fun a b => (if a then Complex.I else 1)*(if a && b then -1 else 1)
  | 3 => Signature.equality

def inverseAxisScale (p : Fin 4) : ℂ :=
  if p=1 ∨ p=2 then (sqrtTwo : ℂ)⁻¹ else 1

def inverseAxis (p : Fin 4) : Kernel ℂ :=
  fun a b => inverseAxisScale p*inverseAxisRaw p a b

theorem inverseAxisScale_ne_zero (p : Fin 4) : inverseAxisScale p≠0 := by
  unfold inverseAxisScale
  split_ifs
  · exact inv_ne_zero (by exact_mod_cast sqrtTwo_ne_zero)
  · exact one_ne_zero

/-- Only two of the twelve fixed physical representatives are needed for
these particular source-normal-form frames. No frame is inserted as a gadget. -/
def selectedSign (p q : Fin 4) : Bool :=
  decide ((p=0 ∧ q=1) ∨ (p=1 ∧ q=2) ∨ (p=2 ∧ (q=0 ∨ q=3)) ∨ (p=3 ∧ q=1))

def selectedRepresentative (p q : Fin 4) : Representative :=
  .inr ![selectedSign p q,false,false]

def selectedKernel (p q : Fin 4) : Kernel ℂ :=
  complexKernel (selectedRepresentative p q)

theorem selectedKernel_actual (p q : Fin 4) : tetrahedralBase (selectedKernel p q) :=
  kernel_base _

def effectiveRaw (p q : Fin 4) : Kernel ℂ :=
  Kernel.mul (fun a b => inverseAxisRaw p b a)
    (Kernel.mul (selectedKernel p q) (inverseAxisRaw q))

def effectiveKernel (p q : Fin 4) : Kernel ℂ :=
  Kernel.mul (fun a b => inverseAxis p b a)
    (Kernel.mul (selectedKernel p q) (inverseAxis q))

theorem effectiveKernel_scale (p q : Fin 4) (a b : Bool) :
    effectiveKernel p q a b=
      (inverseAxisScale p*inverseAxisScale q)*effectiveRaw p q a b := by
  simp only [effectiveKernel,effectiveRaw,inverseAxis,Kernel.mul_apply]
  ring

def effectiveScale : Fin 4 → Fin 4 → ℂ :=
  ![![1+Complex.I,2,2*Complex.I,1+Complex.I],
    ![2*Complex.I,2+2*Complex.I,2+2*Complex.I,2*Complex.I],
    ![2,2+2*Complex.I,-2+2*Complex.I,2],
    ![1+Complex.I,2,2*Complex.I,1+Complex.I]]

def effectiveLinear₀ : Fin 4 → Fin 4 → ZMod 4 :=
  ![![1,3,0,1],![3,0,0,3],![1,0,3,1],![1,3,0,1]]

def effectiveLinear₁ : Fin 4 → Fin 4 → ZMod 4 :=
  ![![0,1,3,0],![3,1,2,3],![0,2,2,0],![0,1,3,0]]

def effectivePhase (p q : Fin 4) : QuadraticPhase 2 where
  constant := 0
  linear := ![effectiveLinear₀ p q,effectiveLinear₁ p q]
  mixed j k := if j=0 ∧ k=1 then 2 else 0
  even_mixed := by intro j k _;split_ifs <;> simp

theorem effectiveScale_ne_zero (p q : Fin 4) : effectiveScale p q≠0 := by
  fin_cases p <;> fin_cases q <;>
    norm_num [effectiveScale,Complex.ext_iff]

/-- Exact amplitudes, including the actual scalar: a full-support quadratic
phase table with even mixed coefficient 2 (hence cross ratio minus one). -/
theorem effectiveRaw_formula (p q : Fin 4) (x : Word 2) :
    effectiveRaw p q (x 0) (x 1)=
      effectiveScale p q*(fourthRootPhase ((effectivePhase p q).eval x) : ℂ) := by
  fin_cases p <;> fin_cases q <;> cases h0 : x 0 <;> cases h1 : x 1
  all_goals simp only [effectivePhase,QuadraticPhase.eval,Fin.sum_univ_succ]
  all_goals norm_num [effectiveRaw,Kernel.mul_apply,inverseAxisRaw,selectedKernel,
    selectedRepresentative,selectedSign,complexKernel,quaternion,signBit,Q0,Q1,Q2,Q3,
    Signature.equality,effectiveScale,effectivePhase,effectiveLinear₀,effectiveLinear₁,
    QuadraticPhase.eval,Fin.sum_univ_succ,bitValue,fourthRootPhase,h0,h1,
    ZMod.val_ofNat,ZMod.val_natCast,ZMod.val_zero,ZMod.val_one_eq_one_mod]
  all_goals (try ring_nf)
  all_goals (try simp [Complex.I_sq])
  all_goals ring

theorem effectiveKernel_formula (p q : Fin 4) (x : Word 2) :
    effectiveKernel p q (x 0) (x 1)=
      (inverseAxisScale p*inverseAxisScale q*effectiveScale p q)*
        (fourthRootPhase ((effectivePhase p q).eval x) : ℂ) := by
  rw [effectiveKernel_scale,effectiveRaw_formula]
  ring

theorem effectiveKernel_full_support (p q : Fin 4) (a b : Bool) :
    effectiveKernel p q a b≠0 := by
  have h := effectiveKernel_formula p q ![a,b]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h
  rw [h]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inverseAxisScale_ne_zero p)
    (inverseAxisScale_ne_zero q)) (effectiveScale_ne_zero p q))
      (by exact_mod_cast fourthRootPhase_ne_zero _)

end
end Holant.Platonic.StabilizerShortening
