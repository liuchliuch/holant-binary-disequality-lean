import Holant.Pauli.ProjectiveDetermination.Line
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! Literal Pauli kernels and the unnormalized real Bell basis. The factor2
records its Gram matrix; no square root or projective normalization is hidden. -/
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace Holant.Pauli.ProjectiveDetermination
open scoped BigOperators ComplexConjugate
abbrev Label := Fin 4
abbrev Local := Bool × Bool

def kernel (g : Label) (a b : Bool) : ℂ :=
  if g = 0 then if a = b then 1 else 0
  else if g = 1 then if a = b then (if a then -1 else 1) else 0
  else if g = 2 then if a = b then 0 else 1
  else if a = b then 0 else if a then -1 else 1

def bell (g : Label) (x : Local) : ℂ := kernel g x.1 x.2

def sign (g j : Label) : ℂ :=
  if g = 0 ∨ j = 0 ∨ g = j then 1 else -1

@[simp] theorem kernel_conj (g : Label) (a b : Bool) : conj (kernel g a b) = kernel g a b := by
  fin_cases g <;> cases a <;> cases b <;> norm_num [kernel]

@[simp] theorem bell_conj (g : Label) (x : Local) : conj (bell g x) = bell g x := kernel_conj g x.1 x.2

theorem bell_orthogonal (j k : Label) :
    ∑ x : Local, bell j x*bell k x = if j = k then 2 else 0 := by
  fin_cases j <;> fin_cases k <;>
    norm_num [bell,kernel,Fintype.sum_prod_type,Fintype.sum_bool]

theorem bell_complete (x y : Local) :
    ∑ j : Label, bell j x*bell j y = if x = y then 2 else 0 := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [bell,kernel,Fin.sum_univ_succ]

/-- Actual two-copy Pauli action has exactly the four manuscript sign rows. -/
theorem paired_eigen (g j : Label) (x : Local) :
    ∑ y : Local, kernel g x.1 y.1*kernel g x.2 y.2*bell j y = sign g j*bell j x := by
  rcases x with ⟨a,b⟩
  fin_cases g <;> fin_cases j <;> cases a <;> cases b <;>
    norm_num [bell,kernel,sign,Fintype.sum_prod_type,Fintype.sum_bool]

/-- The displayed diagonalization is an identity of the actual contraction
kernels, including the skew ZX representative and both original occurrences. -/
theorem paired_expansion (g : Label) (x y : Local) :
    kernel g x.1 y.1*kernel g x.2 y.2 =
      (1/2 : ℂ)*∑ j : Label, sign g j*bell j x*bell j y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  fin_cases g <;> cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [bell,kernel,sign,Fin.sum_univ_succ]

theorem signs_orthogonal (i j : Label) :
    ∑ g : Label, sign g i*sign g j = if i = j then 4 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [sign,Fin.sum_univ_succ]

/-- Four zero Pauli contractions force each repeated Bell-coordinate slice to
vanish. The hypotheses are the four sign equations, derived later from cards. -/
theorem four_sign_equations (z : Label → ℂ) (h : ∀ g : Label, ∑ j : Label, sign g j*z j = 0) :
    ∀ j, z j = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num [sign,Fin.sum_univ_succ] at h0 h1 h2 h3
  intro j
  fin_cases j
  · change z 0 = 0
    linear_combination (1/4 : ℂ)*h0+(1/4 : ℂ)*h1+(1/4 : ℂ)*h2+(1/4 : ℂ)*h3
  · change z 1 = 0
    linear_combination (1/4 : ℂ)*h0+(1/4 : ℂ)*h1-(1/4 : ℂ)*h2-(1/4 : ℂ)*h3
  · change z 2 = 0
    linear_combination (1/4 : ℂ)*h0-(1/4 : ℂ)*h1+(1/4 : ℂ)*h2-(1/4 : ℂ)*h3
  · change z 3 = 0
    linear_combination (1/4 : ℂ)*h0-(1/4 : ℂ)*h1-(1/4 : ℂ)*h2+(1/4 : ℂ)*h3

def localBellSlice (w : Local → Local → ℂ) (j : Label) : ℂ :=
  ∑ x : Local, ∑ y : Local, bell j x*bell j y*w x y

def localPauliSlice (w : Local → Local → ℂ) (g : Label) : ℂ :=
  ∑ x : Local, ∑ y : Local, kernel g x.1 y.1*kernel g x.2 y.2*w x y

/-- The four actual paired kernels span all four equal-index Bell projectors.
This is proved from their literal entries, so no support assumption is inserted. -/
theorem local_diagonal_zero (w : Local → Local → ℂ) (h : ∀ g, localPauliSlice w g = 0) :
    ∀ j, localBellSlice w j = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num [localPauliSlice,kernel,Fintype.sum_prod_type,Fintype.sum_bool] at h0 h1 h2 h3
  intro j
  fin_cases j
  · change localBellSlice w 0 = 0
    norm_num [localBellSlice,bell,kernel,Fintype.sum_prod_type,Fintype.sum_bool]
    linear_combination (1/2 : ℂ)*h0+(1/2 : ℂ)*h1+(1/2 : ℂ)*h2+(1/2 : ℂ)*h3
  · change localBellSlice w 1 = 0
    norm_num [localBellSlice,bell,kernel,Fintype.sum_prod_type,Fintype.sum_bool]
    linear_combination (1/2 : ℂ)*h0+(1/2 : ℂ)*h1-(1/2 : ℂ)*h2-(1/2 : ℂ)*h3
  · change localBellSlice w 2 = 0
    norm_num [localBellSlice,bell,kernel,Fintype.sum_prod_type,Fintype.sum_bool]
    linear_combination (1/2 : ℂ)*h0-(1/2 : ℂ)*h1+(1/2 : ℂ)*h2-(1/2 : ℂ)*h3
  · change localBellSlice w 3 = 0
    norm_num [localBellSlice,bell,kernel,Fintype.sum_prod_type,Fintype.sum_bool]
    linear_combination (1/2 : ℂ)*h0-(1/2 : ℂ)*h1-(1/2 : ℂ)*h2+(1/2 : ℂ)*h3

end Holant.Pauli.ProjectiveDetermination
