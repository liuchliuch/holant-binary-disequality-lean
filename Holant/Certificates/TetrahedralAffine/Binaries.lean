import Holant.Certificates.TetrahedralAffine.Data

/-! All twelve actual tetrahedral binary representatives KX have explicit
witnesses in the same computational-basis affine class as the ancestors. -/
namespace Holant.Certificates.TetrahedralAffine
open Holant Holant.Tractable Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

abbrev Representative := Fin 4 ⊕ (Fin 3 → Bool)

def signA (b : Bool) : AlgebraicComplex := if b then -1 else 1

def kernel : Representative → ABinary
  | .inl k => Q k
  | .inr ε => Q 0 + signA (ε 0) • Q 1 + signA (ε 1) • Q 2 + signA (ε 2) • Q 3

def complexKernel : Representative → Binary
  | .inl k => quaternionBasis k
  | .inr ε => quaternion ![1,signBit (ε 0),signBit (ε 1),signBit (ε 2)]

def binary (r : Representative) : Signature AlgebraicComplex 2 := fun x =>
  Kernel.mul (kernel r) Signature.disequality (x 0) (x 1)

def complexBinary (r : Representative) : Binary := multiply (complexKernel r) X

theorem representative_card : Fintype.card Representative = 12 := by
  norm_num [Fintype.card_sum,Fintype.card_fun]

theorem coe_signA (b : Bool) : (signA b : ℂ) = (signBit b : ℂ) := by cases b <;> simp [signA,signBit]

theorem coe_kernel (r : Representative) (a b : Bool) : (kernel r a b : ℂ) = complexKernel r a b := by
  cases r with
  | inl k => exact coe_Q k a b
  | inr ε => simp [kernel,complexKernel,quaternion,smul_eq_mul,coe_Q,coe_signA,quaternionBasis]

theorem coe_binary (r : Representative) (x : Fin 2 → Bool) :
    (binary r x : ℂ) = complexBinary r (x 0) (x 1) := by
  cases h : x 1 <;> simp [binary,Kernel.mul_disequality,complexBinary,multiply,coe_kernel,X,Signature.disequality,h]

theorem kernel_base (r : Representative) : tetrahedralBase (complexKernel r) := by
  cases r with
  | inl k => exact Or.inl ⟨k,rfl⟩
  | inr ε => exact Or.inr ⟨ε,rfl⟩

theorem base_covered {U : Binary} (h : tetrahedralBase U) : ∃ r : Representative, U = complexKernel r := by
  rcases h with ⟨k,h⟩ | ⟨ε,h⟩
  · exact ⟨.inl k,h⟩
  · exact ⟨.inr ε,h⟩

theorem binary_actual (r : Representative) : groupDirection .tetrahedral (multiply (complexBinary r) X) := by
  rw [complexBinary,multiply_X_twice]
  exact ⟨1,one_ne_zero,_,kernel_base r,by simp⟩

def binarySystem : Representative → AffineSystem 2
  | .inl k => ⟨1,fun _ _ => 1,fun _ => if k = 0 ∨ k = 3 then 1 else 0⟩
  | .inr _ => AffineSystem.unconstrained 2

theorem binarySystem_axis_holds (k : Fin 4) (x : Fin 2 → Bool) :
    (binarySystem (.inl k)).Holds x ↔
      bitValue (ZMod 2) (x 0) + bitValue (ZMod 2) (x 1) = (if k = 0 ∨ k = 3 then 1 else 0) := by
  change (∀ _ : Fin 1, ∑ j : Fin 2, (1 : ZMod 2)*bitValue (ZMod 2) (x j) = _) ↔ _
  simp only [Fin.forall_fin_one,Fin.sum_univ_two,one_mul]
  rfl

theorem binarySystem_sign_holds (ε : Fin 3 → Bool) (x : Fin 2 → Bool) :
    (binarySystem (.inr ε)).Holds x := AffineSystem.unconstrained_holds x

def signLinear (ε : Fin 3 → Bool) : Fin 2 → ZMod 4 :=
  match ε 0,ε 1,ε 2 with
  | false,false,false => ![3,0]
  | false,false,true => ![0,3]
  | false,true,false => ![2,3]
  | false,true,true => ![3,2]
  | true,false,false => ![0,1]
  | true,false,true => ![1,0]
  | true,true,false => ![1,2]
  | true,true,true => ![2,1]

def binaryPhase (r : Representative) : QuadraticPhase 2 where
  constant := 0
  linear := match r with
    | .inl k => if k = 2 ∨ k = 3 then ![2,0] else fun _ => 0
    | .inr ε => signLinear ε
  mixed := fun j k => match r with
    | .inl _ => 0
    | .inr _ => if j = 0 ∧ k = 1 then 2 else 0
  even_mixed := by
    intro j k _
    cases r with
    | inl _ => exact Or.inl rfl
    | inr _ =>
      by_cases h : j = 0 ∧ k = 1
      · exact Or.inr (if_pos h)
      · exact Or.inl (if_neg h)

def binaryScale : Representative → AlgebraicComplex
  | .inl k => if k = 1 ∨ k = 3 then imaginaryUnit else 1
  | .inr ε => signA (ε 1) + signA (ε 0)*imaginaryUnit

theorem binary_formula (r : Representative) :
    binary r = affineFormula (binaryScale r) (binarySystem r) (binaryPhase r) := by
  have ztwo : (2 : ZMod 2) = 0 := by decide
  cases r with
  | inl k =>
    fin_cases k <;> funext x <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp only [affineFormula,binaryPhase,QuadraticPhase.eval,Fin.sum_univ_succ] <;>
      norm_num [binary,kernel,Q,Kernel.mul_disequality,Signature.equality,
        affineFormula,binaryScale,binarySystem_axis_holds,binaryPhase,
        QuadraticPhase.eval,Fin.sum_univ_succ,Fin.forall_fin_succ,bitValue,fourthRootPhase,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.natCast_self,ztwo,imaginaryUnit_sq,imaginaryUnit_pow_three,h0,h1] <;> simp [ztwo]
  | inr ε =>
    cases e0 : ε 0 <;> cases e1 : ε 1 <;> cases e2 : ε 2 <;>
      funext x <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp only [affineFormula,binaryPhase,QuadraticPhase.eval,Fin.sum_univ_succ] <;>
      norm_num [binary,kernel,Q,Kernel.mul_disequality,Signature.equality,signA,smul_eq_mul,
        affineFormula,binaryScale,binarySystem_sign_holds,
        binaryPhase,signLinear,QuadraticPhase.eval,Fin.sum_univ_succ,Fin.forall_fin_succ,
        bitValue,fourthRootPhase,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.natCast_self,ztwo,imaginaryUnit_sq,imaginaryUnit_pow_three,h0,h1,e0,e1,e2] <;>
      (try ring_nf) <;> norm_num [imaginaryUnit_sq,ZMod.val_ofNat,ZMod.val_natCast,ZMod.val_one_eq_one_mod,ZMod.val_zero] <;> (first | rfl | ring | skip)

theorem binary_affine (r : Representative) : Affine (binary r) := by
  rw [binary_formula]
  exact affine_formula _ _ _

end
end Holant.Certificates.TetrahedralAffine
