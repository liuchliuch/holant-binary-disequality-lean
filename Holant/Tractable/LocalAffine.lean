import Holant.Tractable.Affine
import Holant.BoundaryAction

/-!
Exact local-affine definition (authoritative manuscript, lines 2080–2095).
`phaseMatrix` is `diag(1, ζ₈)` for the certified source choice in `Scalars`.
A support bit selects its zeroth or first matrix power at the corresponding
ordered port; `coordinateAction` is the existing full tensor-product action.
-/

namespace Holant.Tractable

noncomputable section

/-- The source's matrix `T₂ = diag(1, ζ₈)`. -/
def phaseMatrix : Kernel AlgebraicComplex := fun a b =>
  if a = b then (if a then zetaEight else 1) else 0

/-- Since the exponent is a bit, this is exactly `T₂ ^ αⱼ`. -/
def localPhaseMatrix (b : Bool) : Kernel AlgebraicComplex :=
  if b then phaseMatrix else Signature.equality

/-- Apply the local phases selected by a Boolean support assignment. -/
def localTwist {n : ℕ} (alpha : Fin n → Bool) (f : Signature AlgebraicComplex n) :
    Signature AlgebraicComplex n :=
  Signature.coordinateAction (fun j => localPhaseMatrix (alpha j)) f

/-- Membership tests every support assignment, in the displayed coordinates. -/
def LocalAffine {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∀ alpha : Fin n → Bool, f alpha ≠ 0 → Affine (localTwist alpha f)

@[simp] theorem localAffine_zero (n : ℕ) : LocalAffine (0 : Signature AlgebraicComplex n) := by
  intro alpha h
  exact False.elim (h rfl)

@[simp] theorem localTwist_false {n : ℕ} (f : Signature AlgebraicComplex n) :
    localTwist (fun _ => false) f = f := by
  exact Signature.coordinateAction_equality f

@[simp] theorem localTwist_scalar (alpha : Fin 0 → Bool) (c : AlgebraicComplex) :
    localTwist alpha (Signature.scalar c) = Signature.scalar c :=
  Signature.coordinateAction_scalar _ _

/-- Nullary signatures retain their scalar, and all are locally affine. -/
theorem localAffine_scalar (c : AlgebraicComplex) : LocalAffine (Signature.scalar c) := by
  intro alpha _
  rw [localTwist_scalar]
  exact affine_constant 0 c

theorem localTwist_scale {n : ℕ} (alpha : Fin n → Bool)
    (f : Signature AlgebraicComplex n) (c : AlgebraicComplex) :
    localTwist alpha (fun x => c * f x) = fun x => c * localTwist alpha f x := by
  funext x
  simp only [localTwist, Signature.coordinateAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Scaling preserves the support implication, including the zero scale. -/
theorem LocalAffine.scale {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : LocalAffine f) (c : AlgebraicComplex) : LocalAffine (fun x => c * f x) := by
  intro alpha h
  have hfa : f alpha ≠ 0 := by
    intro hzero
    exact h (by simp only [hzero, mul_zero])
  rw [localTwist_scale]
  exact (hf alpha hfa).scale c

/-- Hamming weight of an ordered Boolean assignment. -/
def weight {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ j, if x j then 1 else 0

/-- The source's class `ℳ`: entries above Hamming weight one vanish. -/
def AtMostOneSupport {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∀ x, 1 < weight x → f x = 0

@[simp] theorem atMostOneSupport_zero (n : ℕ) :
    AtMostOneSupport (0 : Signature AlgebraicComplex n) := by intro x _; rfl

theorem AtMostOneSupport.scale {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : AtMostOneSupport f) (c : AlgebraicComplex) :
    AtMostOneSupport (fun x => c * f x) := by
  intro x hx
  simp only [hf x hx, mul_zero]

end
end Holant.Tractable
