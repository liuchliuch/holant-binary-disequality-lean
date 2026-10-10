import Holant.Kernel
import Holant.Algebraic.GaussianEmbedding
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Literal exotic Klein matrices and their exact nonzero scalar factors.
Labels are the actual additive group F₂² in source order00,01,10,11. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators
abbrev Label := ZMod 2 × ZMod 2
abbrev Mat := Kernel ℂ

def xLabel : Label := (0,1)
def yLabel : Label := (1,0)
def zLabel : Label := (1,1)

theorem label_cases (a : Label) : a = 0 ∨ a = xLabel ∨ a = yLabel ∨ a = zLabel := by
  rcases a with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> decide

@[simp] theorem two_zmod : (2 : ZMod 2) = 0 := by decide
@[simp] theorem label_zero : (0 : Label) = ((0 : ZMod 2),0) := rfl

def theta (a : Label) : Label := (a.1,a.1+a.2)

@[simp] theorem theta_zero : theta 0 = 0 := rfl
@[simp] theorem theta_theta (a : Label) : theta (theta a) = a := by
  rcases a with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> decide

theorem theta_add (a b : Label) : theta (a+b) = theta a+theta b := by
  apply Prod.ext
  · rfl
  · change (a.1+b.1)+(a.2+b.2) = (a.1+a.2)+(b.1+b.2)
    abel

theorem label_add_self (a : Label) : a+a = 0 := by
  rcases a with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> decide

@[simp] theorem theta_x : theta xLabel = xLabel := by decide
@[simp] theorem theta_y : theta yLabel = zLabel := by decide
@[simp] theorem theta_z : theta zLabel = yLabel := by decide
@[simp] theorem xx : xLabel+xLabel = 0 := by decide
@[simp] theorem yy : yLabel+yLabel = 0 := by decide
@[simp] theorem zz : zLabel+zLabel = 0 := by decide
@[simp] theorem xy : xLabel+yLabel = zLabel := by decide
@[simp] theorem yx : yLabel+xLabel = zLabel := by decide
@[simp] theorem xz : xLabel+zLabel = yLabel := by decide
@[simp] theorem zx : zLabel+xLabel = yLabel := by decide
@[simp] theorem yz : yLabel+zLabel = xLabel := by decide
@[simp] theorem zy : zLabel+yLabel = xLabel := by decide
@[simp] theorem x_ne_zero : xLabel ≠ 0 := by decide
@[simp] theorem y_ne_zero : yLabel ≠ 0 := by decide
@[simp] theorem z_ne_zero : zLabel ≠ 0 := by decide
@[simp] theorem zero_ne_x : (0 : Label) ≠ xLabel := by decide
@[simp] theorem zero_ne_y : (0 : Label) ≠ yLabel := by decide
@[simp] theorem zero_ne_z : (0 : Label) ≠ zLabel := by decide
@[simp] theorem x_ne_y : xLabel ≠ yLabel := by decide
@[simp] theorem x_ne_z : xLabel ≠ zLabel := by decide
@[simp] theorem y_ne_z : yLabel ≠ zLabel := by decide

/-- Uniform entry formulas over any coefficient ring; the chosen generator
becomes the actual complex i in E and the exact Gaussian generator in gaussianE. -/
def EOver {K : Type*} [Ring K] (i : K) (a : Label) : Kernel K :=
  if a = 0 then fun x y => if x = y then 1 else 0
  else if a = xLabel then fun x y => if x = y then 0 else 1
  else if a = yLabel then fun x y =>
    if x then (if y then -i else -1) else (if y then 1 else i)
  else fun x y => if x then (if y then i else -1) else (if y then 1 else -i)

def E : Label → Mat := EOver Complex.I

@[simp] theorem E_zero (x y : Bool) : E 0 x y = if x = y then 1 else 0 := rfl
@[simp] theorem E_x (x y : Bool) : E xLabel x y = if x = y then 0 else 1 := rfl
@[simp] theorem E_y (x y : Bool) : E yLabel x y =
    if x then (if y then -Complex.I else -1) else (if y then 1 else Complex.I) := rfl
@[simp] theorem E_z (x y : Bool) : E zLabel x y =
    if x then (if y then Complex.I else -1) else (if y then 1 else -Complex.I) := rfl

def dOver {K : Type*} [Ring K] (a : Label) : K := if a.1 = 0 then 2 else 4

def d (a : Label) : ℂ := dOver a

def transposeScalar (a : Label) : ℂ := if a.1 = 0 then 1 else -1

def scale (c : ℂ) (A : Mat) : Mat := fun x y => c*A x y

def omega (a b : Label) : ℂ :=
  if a = 0 ∨ b = 0 then 1
  else if a = xLabel then if b = xLabel then 1 else if b = yLabel then -Complex.I else Complex.I
  else if a = yLabel then if b = xLabel then Complex.I else if b = yLabel then -2 else 2*Complex.I
  else if b = xLabel then -Complex.I else if b = yLabel then -2*Complex.I else -2

@[simp] theorem d_ne_zero (a : Label) : d a ≠ 0 := by
  unfold d dOver
  split_ifs <;> norm_num

@[simp] theorem d_theta (a : Label) : d (theta a) = d a := rfl
@[simp] theorem transposeScalar_ne_zero (a : Label) : transposeScalar a ≠ 0 := by
  unfold transposeScalar
  split_ifs <;> norm_num

theorem omega_ne_zero (a b : Label) : omega a b ≠ 0 := by
  rcases label_cases a with rfl | rfl | rfl | rfl <;>
    rcases label_cases b with rfl | rfl | rfl | rfl <;>
    norm_num [omega,xLabel,yLabel,zLabel]

/-- Exact bilinear Frobenius Gram matrix, including the exotic swap2↔3. -/
theorem gram (a b : Label) : Kernel.pair (E a) (E b) = d a*(if b = theta a then 1 else 0) := by
  rcases label_cases a with rfl | rfl | rfl | rfl <;>
    rcases label_cases b with rfl | rfl | rfl | rfl <;>
    simp only [theta_zero,theta_x,theta_y,theta_z,zero_ne_x,zero_ne_y,zero_ne_z,Kernel.pair,Fintype.sum_bool,E_zero,E_x,E_y,E_z] <;>
    norm_num [d,dOver,xLabel,yLabel,zLabel,label_zero,Prod.mk.injEq]

/-- The scalar is retained literally, rather than removed by projectivization. -/
theorem transpose_E (a : Label) : Kernel.transpose (E a) = scale (transposeScalar a) (E (theta a)) := by
  funext x y
  rcases label_cases a with rfl | rfl | rfl | rfl <;>
    simp only [theta_zero,theta_x,theta_y,theta_z,Kernel.transpose_apply,scale,E_zero,E_x,E_y,E_z] <;>
    cases x <;> cases y <;> norm_num [transposeScalar,xLabel,yLabel,zLabel]

/-- Exact source fusion law and its recorded nonzero multiplier. -/
theorem fusion (a b : Label) : Kernel.mul (E a) (E b) = scale (omega a b) (E (a+b)) := by
  funext x y
  rcases label_cases a with rfl | rfl | rfl | rfl <;>
    rcases label_cases b with rfl | rfl | rfl | rfl <;>
    simp only [zero_add,add_zero,xx,yy,zz,xy,yx,xz,zx,yz,zy,Kernel.mul_apply,scale,E_zero,E_x,E_y,E_z] <;>
    cases x <;> cases y <;> norm_num [omega,xLabel,yLabel,zLabel,label_zero,Prod.mk.injEq] <;> ring

theorem trace_E (a : Label) : Kernel.trace (E a) = if a = 0 then 2 else 0 := by
  rcases label_cases a with rfl | rfl | rfl | rfl <;>
    norm_num [E,EOver,xLabel,yLabel,zLabel,Kernel.trace,Fintype.sum_bool]

def dualOver {K : Type*} [Field K] (i : K) (a : Label) : Kernel K :=
  fun x y => (dOver a)⁻¹*EOver i (theta a) x y

def dual (a : Label) : Mat := dualOver Complex.I a

/-- Actual dual pairing, so these four representatives form a faithful basis. -/
theorem dual_pair (a b : Label) : Kernel.pair (dual a) (E b) = if a = b then 1 else 0 := by
  change (∑ x : Bool, ∑ y : Bool, (d a)⁻¹*E (theta a) x y*E b x y) = _
  simp_rw [_root_.mul_assoc,← Finset.mul_sum]
  change (d a)⁻¹*Kernel.pair (E (theta a)) (E b) = _
  rw [gram,d_theta,theta_theta]
  by_cases h : a = b
  · subst b; simp
  · simp [h,Ne.symm h]

def gaussianI : Algebraic.GaussianRational := ⟨0,1⟩
def gaussianE (a : Label) : Kernel Algebraic.GaussianRational := EOver gaussianI a
def gaussianDual (a : Label) : Kernel Algebraic.GaussianRational := dualOver gaussianI a

@[simp] theorem map_gaussianI : Algebraic.gaussianToComplex gaussianI = Complex.I := by
  simp [gaussianI]

@[simp] theorem map_gaussianE (a : Label) (x y : Bool) :
    Algebraic.gaussianToComplex (gaussianE a x y) = E a x y := by
  unfold gaussianE E EOver
  split_ifs <;> cases x <;> cases y <;>
    simp [map_gaussianI, -Algebraic.gaussianToComplex_apply]

@[simp] theorem map_gaussianDual (a : Label) (x y : Bool) :
    Algebraic.gaussianToComplex (gaussianDual a x y) = dual a x y := by
  have hd : Algebraic.gaussianToComplex (dOver (K := Algebraic.GaussianRational) a) = d a := by
    unfold d dOver
    split_ifs <;> exact map_ofNat _ _
  change Algebraic.gaussianToComplex ((dOver a)⁻¹*gaussianE (theta a) x y) = (d a)⁻¹*E (theta a) x y
  rw [map_mul,map_inv₀,hd,map_gaussianE]

end
end Holant.Pauli.ExoticKlein
