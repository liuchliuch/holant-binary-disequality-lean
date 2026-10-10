import Holant.Pauli.ExoticKlein.Basic

/-! Faithful exotic binary and quaternary basis coordinates. Every coefficient
is the actual bilinear contraction against the displayed Frobenius duals. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open scoped BigOperators

def labelEquiv : Fin 4 ≃ Label where
  toFun j := ![0,xLabel,yLabel,zLabel] j
  invFun a := if a = 0 then 0 else if a = xLabel then 1 else if a = yLabel then 2 else 3
  left_inv j := by fin_cases j <;> decide
  right_inv a := by rcases label_cases a with rfl|rfl|rfl|rfl <;> decide

theorem sum_labels {K : Type*} [AddCommMonoid K] (f : Label → K) :
    ∑ a, f a = f 0+f xLabel+f yLabel+f zLabel := by
  have h := Fintype.sum_equiv labelEquiv (fun j => f (labelEquiv j)) f (fun _ => rfl)
  simpa [labelEquiv,Fin.sum_univ_succ,add_assoc] using h.symm

@[simp] theorem d_zero : d 0 = 2 := rfl
@[simp] theorem d_x : d xLabel = 2 := rfl
@[simp] theorem d_y : d yLabel = 4 := rfl
@[simp] theorem d_z : d zLabel = 4 := rfl

@[simp] theorem dual_apply (a : Label) (x y : Bool) : dual a x y = (d a)⁻¹*E (theta a) x y := rfl

/-- Literal completeness of the binary Frobenius-dual basis. -/
theorem dual_complete (x y u v : Bool) :
    ∑ a : Label, E a x y*dual a u v = if x = u ∧ y = v then 1 else 0 := by
  rw [sum_labels]
  simp only [dual_apply,theta_zero,theta_x,theta_y,theta_z,d_zero,d_x,d_y,d_z,E_zero,E_x,E_y,E_z]
  cases x <;> cases y <;> cases u <;> cases v <;> norm_num <;> ring_nf <;> norm_num <;> ring

theorem binary_reconstruction (T : Mat) (x y : Bool) :
    ∑ a : Label, Kernel.pair (dual a) T*E a x y = T x y := by
  rw [sum_labels]
  simp only [Kernel.pair,Fintype.sum_bool,dual_apply,theta_zero,theta_x,theta_y,theta_z,
    d_zero,d_x,d_y,d_z,E_zero,E_x,E_y,E_z]
  cases x <;> cases y <;> norm_num <;> ring_nf <;> norm_num <;> ring

abbrev Four (K : Type*) := Bool → Bool → Bool → Bool → K

def baseOver {K : Type*} [Field K] (i : K) (a b : Label) : Four K :=
  fun x y z w => EOver i a x y*EOver i b z w

def crossOver {K : Type*} [Field K] (i : K) (a b : Label) : Four K :=
  fun x y z w => EOver i a x z*EOver i b y w

def parallelOver {K : Type*} [Field K] (i : K) (a b : Label) : Four K :=
  fun x y z w => EOver i a x w*EOver i b y z

def base := baseOver Complex.I
def cross := crossOver Complex.I
def parallel := parallelOver Complex.I

def firstCardOver {K : Type*} [Field K] (i : K) (a : Label) (T : Four K) : Kernel K :=
  fun z w => ∑ x : Bool, ∑ y : Bool, dualOver i a x y*T x y z w

def coefficientOver {K : Type*} [Field K] (i : K) (T : Four K) (a b : Label) : K :=
  Kernel.pair (dualOver i b) (firstCardOver i a T)

def coefficient (T : Four ℂ) (a b : Label) : ℂ := coefficientOver Complex.I T a b

/-- Ordered two-pair tomography follows from the actual binary basis twice. -/
theorem reconstruction (T : Four ℂ) (x y z w : Bool) :
    ∑ a : Label, ∑ b : Label, coefficient T a b*base a b x y z w = T x y z w := by
  change (∑ a : Label, ∑ b : Label,
    Kernel.pair (dual b) (firstCardOver Complex.I a T)*(E a x y*E b z w)) = _
  calc
    _ = ∑ a : Label, E a x y*(∑ b : Label, Kernel.pair (dual b) (firstCardOver Complex.I a T)*E b z w) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ a : Label, E a x y*firstCardOver Complex.I a T z w := by simp_rw [binary_reconstruction]
    _ = ∑ a : Label, Kernel.pair (dual a) (fun u v => T u v z w)*E a x y := by
      apply Finset.sum_congr rfl
      intro a ha
      exact mul_comm _ _
    _ = T x y z w := binary_reconstruction _ x y

end
end Holant.Pauli.ExoticKlein
