import Holant.Tractable.AffineOperations


namespace Holant.LocalDrafts.Tractability.AffineMachine.Reconstruction

noncomputable section

open Holant.Tractable AffinePhase TwoTranslate
open scoped BigOperators

variable {n : ℕ}

def mixedCoefficient (q : Word n → ZMod 4) (j k : Fin n) : ZMod 4 :=
  q (xor (basis j) (basis k)) - q (basis j) - q (basis k) + q (origin n)

theorem mixed_comm (q : Word n → ZMod 4) (j k : Fin n) :
    mixedCoefficient q j k = mixedCoefficient q k j := by
  unfold mixedCoefficient
  rw [AffinePhase.xor_comm (basis j) (basis k)]
  ring

theorem mixed_even (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) (j k : Fin n) :
    mixedCoefficient q j k = 0 ∨ mixedCoefficient q j k = 2 := by
  have h := hq (origin n) (basis j) (basis k) (basis k)
  simp only [thirdDifference, origin_xor, AffinePhase.xor_self,
    xor_cancel_right] at h
  have he : 2 * mixedCoefficient q j k = 0 := by
    unfold mixedCoefficient
    linear_combination -h
  have even4 : ∀ a : ZMod 4, 2 * a = 0 → a = 0 ∨ a = 2 := by decide
  exact even4 _ he

/-- All stored coefficients are explicit values of a fixed finite sample list.
The proof of even mixed entries has no computational role. -/
def coefficients (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) : QuadraticPhase n where
  constant := q (origin n)
  linear j := q (basis j) - q (origin n)
  mixed := mixedCoefficient q
  even_mixed j k _ := mixed_even q hq j k

theorem eval_origin (Q : QuadraticPhase n) : Q.eval (origin n) = Q.constant := by
  simp [QuadraticPhase.eval, origin]

theorem eval_basis (Q : QuadraticPhase n) (j : Fin n) :
    Q.eval (basis j) = Q.constant + Q.linear j := by
  have hw : basis j = word ({j} : Finset (Fin n)) := by
    funext i
    simp [basis, word]
  rw [hw, quadratic_eval_word]
  simp

theorem basis_pair_word (j k : Fin n) (h : j ≠ k) :
    xor (basis j) (basis k) = word ({j, k} : Finset (Fin n)) := by
  funext i
  by_cases hij : i = j <;> by_cases hik : i = k <;>
    simp_all [AffinePhase.xor, basis, word]

theorem eval_pair (Q : QuadraticPhase n) (j k : Fin n) (h : j < k) :
    Q.eval (xor (basis j) (basis k)) =
      Q.constant + Q.linear j + Q.linear k + Q.mixed j k := by
  rw [basis_pair_word j k (ne_of_lt h), quadratic_eval_word]
  simp [ne_of_lt h, ne_of_gt h, h, not_lt_of_gt h]
  ring

theorem samples (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) :
    (coefficients q hq).eval (origin n) = q (origin n) ∧
    (∀ j, (coefficients q hq).eval (basis j) = q (basis j)) ∧
    (∀ j k, (coefficients q hq).eval (xor (basis j) (basis k)) = q (xor (basis j) (basis k))) := by
  refine ⟨eval_origin _, ?_, ?_⟩
  · intro j
    rw [eval_basis]
    simp [coefficients]
  · intro j k
    rcases lt_trichotomy j k with h | rfl | h
    · rw [eval_pair _ j k h]
      simp only [coefficients, mixedCoefficient]
      ring
    · simp only [AffinePhase.xor_self, eval_origin, coefficients]
    · rw [AffinePhase.xor_comm (basis j) (basis k), eval_pair _ k j h]
      simp only [coefficients, mixedCoefficient]
      ring

/-- A vanishing-third-difference function is determined by the listed samples.
The proof uses induction on supports; this induction is not the evaluator. -/
theorem zero_of_samples (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0)
    (h0 : q (origin n) = 0) (h1 : ∀ j, q (basis j) = 0)
    (h2 : ∀ j k, q (xor (basis j) (basis k)) = 0) : ∀ x, q x = 0 := by
  have derivative (j : Fin n) (x : Word n) : q (xor x (basis j)) - q x = 0 := by
    let d := fun y => q (xor y (basis j)) - q y
    have hd0 : d (origin n) = 0 := by simp [d, h0, h1]
    have hd (y z : Word n) : d (xor y z) = d y + d z := by
      have h := hq (origin n) y z (basis j)
      simp only [thirdDifference, origin_xor, h0, h1] at h
      dsimp [d]
      linear_combination h
    have heq : d = fun _ => (0 : ZMod 4) := additive_word_eq d (fun _ => 0)
      hd0 rfl hd (by intros; simp) (by intro k; simp [d, h1, h2])
    exact congrFun heq x
  have hw (s : Finset (Fin n)) : q (word s) = 0 := by
    induction s using Finset.induction_on with
    | empty => simpa [word, origin] using h0
    | @insert j s hj ih =>
      rw [word_insert s j hj]
      exact (sub_eq_zero.mp (derivative j (word s))).trans ih
  intro x
  let s := Finset.univ.filter (fun j => x j = true)
  have hs : word s = x := by funext j; simp [word, s]
  simpa only [hs] using hw s

theorem eval_coefficients (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) (x : Word n) :
    (coefficients q hq).eval x = q x := by
  let Q := coefficients q hq
  have hz : ∀ z u v w, thirdDifference (fun x => Q.eval x - q x) z u v w = 0 := by
    intro z u v w
    have hQ := quadratic_thirdDifference Q z u v w
    have h := hq z u v w
    unfold thirdDifference at *
    linear_combination hQ - h
  have hs := samples q hq
  exact sub_eq_zero.mp (zero_of_samples (fun x => Q.eval x - q x) hz
    (by rw [hs.1]; simp) (by intro j; rw [hs.2.1]; simp)
    (by intro j k; rw [hs.2.2]; simp) x)

theorem precompose_third {m : ℕ} (Q : QuadraticPhase n) (p : Word m → Word n)
    (hp : IsAffineMap p) (z u v w : Word m) :
    thirdDifference (fun x => Q.eval (p x)) z u v w = 0 := by
  have h := quadratic_thirdDifference Q (p z)
    (xor (p u) (p (origin m))) (xor (p v) (p (origin m))) (xor (p w) (p (origin m)))
  -- Fold each translated step back to p (x XOR y), from the inside out.
  -- Rewriting hp forward would leave the nested translated words unmatched.
  have translate (x y : Word m) :
      xor (p x) (xor (p y) (p (origin m))) = p (xor x y) := (hp x y).symm
  simpa only [thirdDifference, translate] using h

def pullback {m : ℕ} (Q : QuadraticPhase n) (p : Word m → Word n) (hp : IsAffineMap p) :
    QuadraticPhase m := coefficients (fun x => Q.eval (p x)) (precompose_third Q p hp)

theorem pullback_eval {m : ℕ} (Q : QuadraticPhase n) (p : Word m → Word n)
    (hp : IsAffineMap p) (x : Word m) : (pullback Q p hp).eval x = Q.eval (p x) :=
  eval_coefficients _ _ x

def addParity (Q : QuadraticPhase n) (a : Fin n → ZMod 2) (t : ZMod 4) : QuadraticPhase n :=
  coefficients (fun x => Q.eval x + t * bitLift (dot a x)) (by
    intro z u v w
    rw [thirdDifference_add, quadratic_thirdDifference, thirdDifference_mul_const, bitLift_dot_thirdDifference]
    simp)

theorem addParity_eval (Q : QuadraticPhase n) (a : Fin n → ZMod 2) (t : ZMod 4) (x : Word n) :
    (addParity Q a t).eval x = Q.eval x + t * bitLift (dot a x) := eval_coefficients _ _ x

/-- Conservative sample-call count of the literal coefficient expressions:
one constant, two calls per linear slot, four per stored mixed slot. -/
def sampleCalls (n : ℕ) := 1 + 2 * n + 4 * n * n

end
end Holant.LocalDrafts.Tractability.AffineMachine.Reconstruction
