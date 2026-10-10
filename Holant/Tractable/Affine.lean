import Holant.Tractable.Scalars
import Holant.Signature
import Mathlib.Data.ZMod.Basic

/-!
Exact source-level affine class, manuscript `eq:affine-class` (lines 1896–1916
of the authoritative 2026-09-27 rewrite). Supports are finite systems `Ax=b`
over `ZMod 2`, including zero rows. Phases are genuine `ZMod 4` quadratics;
only strictly ordered pairs contribute and each mixed coefficient is `0` or `2`.
Zero is admitted separately, while every displayed scale witness is nonzero.
These are semantic predicates, not membership algorithms or tractability proofs.
-/

namespace Holant.Tractable

noncomputable section

/-- Interpret a Boolean coordinate as `0` or `1` in the chosen ring. -/
def bitValue (R : Type*) [Zero R] [One R] (b : Bool) : R := if b then 1 else 0

@[simp] theorem bitValue_false (R : Type*) [Zero R] [One R] :
    bitValue R false = 0 := rfl
@[simp] theorem bitValue_true (R : Type*) [Zero R] [One R] :
    bitValue R true = 1 := rfl

/-- A finite affine system, with explicit row count and binary coefficients. -/
structure AffineSystem (n : ℕ) where
  rows : ℕ
  matrix : Fin rows → Fin n → ZMod 2
  rhs : Fin rows → ZMod 2

namespace AffineSystem

variable {n : ℕ}

def Holds (S : AffineSystem n) (x : Fin n → Bool) : Prop :=
  ∀ row, ∑ j, S.matrix row j * bitValue (ZMod 2) (x j) = S.rhs row

instance (S : AffineSystem n) (x : Fin n → Bool) : Decidable (S.Holds x) := by
  unfold Holds
  infer_instance

/-- No equations means the full Boolean cube, also at arity zero. -/
def unconstrained (n : ℕ) : AffineSystem n := ⟨0, Fin.elim0, Fin.elim0⟩

@[simp] theorem unconstrained_holds (x : Fin n → Bool) :
    (unconstrained n).Holds x := fun row => Fin.elim0 row

end AffineSystem

/-- The source's multilinear quadratic representative modulo four. -/
structure QuadraticPhase (n : ℕ) where
  constant : ZMod 4
  linear : Fin n → ZMod 4
  mixed : Fin n → Fin n → ZMod 4
  even_mixed : ∀ j k, j < k → mixed j k = 0 ∨ mixed j k = 2

namespace QuadraticPhase

variable {n : ℕ}

def eval (Q : QuadraticPhase n) (x : Fin n → Bool) : ZMod 4 :=
  Q.constant + (∑ j, Q.linear j * bitValue (ZMod 4) (x j)) +
    ∑ j, ∑ k, if j < k then
      Q.mixed j k * bitValue (ZMod 4) (x j) * bitValue (ZMod 4) (x k) else 0

def zero (n : ℕ) : QuadraticPhase n :=
  ⟨0, fun _ => 0, fun _ _ => 0, fun _ _ _ => Or.inl rfl⟩

@[simp] theorem zero_eval (x : Fin n → Bool) : (zero n).eval x = 0 := by
  simp [eval, zero]

end QuadraticPhase

/-- Fourth-root phase of a residue, using its canonical representative `0,…,3`. -/
def fourthRootPhase (q : ZMod 4) : AlgebraicComplex := imaginaryUnit ^ q.val

@[simp] theorem fourthRootPhase_zero : fourthRootPhase 0 = 1 := by
  simp [fourthRootPhase]

@[simp] theorem fourthRootPhase_pow_four (q : ZMod 4) : fourthRootPhase q ^ 4 = 1 := by
  calc
    fourthRootPhase q ^ 4 = (imaginaryUnit ^ 4) ^ q.val := by
      simp only [fourthRootPhase, ← pow_mul, Nat.mul_comm]
    _ = 1 := by rw [imaginaryUnit_pow_four, one_pow]

theorem fourthRootPhase_ne_zero (q : ZMod 4) : fourthRootPhase q ≠ 0 := by
  intro h
  have hp := fourthRootPhase_pow_four q
  rw [h] at hp
  norm_num at hp

/-- The displayed source formula, without dropping the scale or coordinates. -/
def affineFormula {n : ℕ} (scale : AlgebraicComplex) (S : AffineSystem n)
    (Q : QuadraticPhase n) : Signature AlgebraicComplex n := fun x =>
  if S.Holds x then scale * fourthRootPhase (Q.eval x) else 0

/-- The manuscript's affine class `𝒜`, including zero. -/
def Affine {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  f = 0 ∨ ∃ scale : AlgebraicComplex, scale ≠ 0 ∧
    ∃ S : AffineSystem n, ∃ Q : QuadraticPhase n, f = affineFormula scale S Q

@[simp] theorem affine_zero (n : ℕ) : Affine (0 : Signature AlgebraicComplex n) :=
  Or.inl rfl

theorem affine_formula {n : ℕ} (scale : AlgebraicComplex) (S : AffineSystem n)
    (Q : QuadraticPhase n) : Affine (affineFormula scale S Q) := by
  by_cases hs : scale = 0
  · left
    subst scale
    funext x
    simp [affineFormula]
  · exact Or.inr ⟨scale, hs, S, Q, rfl⟩

/-- Every constant signature, including every actual nullary scalar, is affine. -/
theorem affine_constant (n : ℕ) (c : AlgebraicComplex) :
    Affine (fun _ : Fin n → Bool => c) := by
  convert affine_formula c (AffineSystem.unconstrained n) (QuadraticPhase.zero n) using 1
  funext x
  simp [affineFormula]

/-- Every affine-system indicator is included with the trivial phase. -/
theorem affine_indicator {n : ℕ} (S : AffineSystem n) :
    Affine (fun x => if S.Holds x then (1 : AlgebraicComplex) else 0) := by
  convert affine_formula 1 S (QuadraticPhase.zero n) using 1
  funext x
  simp [affineFormula]

/-- Scaling closure keeps an actual nonzero witness whenever the scale is nonzero. -/
theorem Affine.scale {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Affine f)
    (c : AlgebraicComplex) : Affine (fun x => c * f x) := by
  rcases hf with rfl | ⟨s, hs, S, Q, rfl⟩
  · left
    funext x
    simp
  · convert affine_formula (c * s) S Q using 1
    funext x
    simp only [affineFormula]
    split <;> simp [mul_assoc]

/-- Nonzero entries of an affine signature have the same fourth power.
This nontrivial necessary condition rules out arbitrary complex-valued tables. -/
theorem Affine.fourth_power_eq {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Affine f) (x y : Fin n → Bool) (hx : f x ≠ 0) (hy : f y ≠ 0) :
    f x ^ 4 = f y ^ 4 := by
  rcases hf with rfl | ⟨s, hs, S, Q, rfl⟩
  · exact False.elim (hx rfl)
  · have hSx : S.Holds x := by
      by_contra hn
      exact hx (by simp [affineFormula, hn])
    have hSy : S.Holds y := by
      by_contra hn
      exact hy (by simp [affineFormula, hn])
    simp [affineFormula, hSx, hSy, mul_pow]

end
end Holant.Tractable
