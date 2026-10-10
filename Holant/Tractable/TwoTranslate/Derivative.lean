import Holant.Tractable.AffinePhaseCriterion

/-! Additive derivatives of the manuscript's exact quadratic phases. -/
namespace Holant.Tractable
noncomputable section
namespace TwoTranslate
open AffinePhase

/-- The additive embedding from the binary group into the even residues modulo four. -/
def evenLift (a : ZMod 2) : ZMod 4 := if a = 0 then 0 else 2

@[simp] theorem evenLift_zero : evenLift 0 = 0 := by simp [evenLift]
@[simp] theorem evenLift_one : evenLift 1 = 2 := by simp [evenLift]

theorem evenLift_add (a b : ZMod 2) : evenLift (a + b) = evenLift a + evenLift b := by
  fin_cases a <;> fin_cases b <;> decide

theorem evenLift_sum {ι : Type*} (s : Finset ι) (a : ι → ZMod 2) :
    evenLift (∑ j ∈ s, a j) = ∑ j ∈ s, evenLift (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [hj, evenLift_add, ih]

theorem bitValue_xor_two (a b : Bool) :
    bitValue (ZMod 2) (Bool.xor a b) = bitValue (ZMod 2) a + bitValue (ZMod 2) b := by
  cases a <;> cases b <;> decide

/-- A binary linear form in the original input coordinates. -/
def dot {n : ℕ} (a : Fin n → ZMod 2) (x : Word n) : ZMod 2 :=
  ∑ j, a j * bitValue (ZMod 2) (x j)

@[simp] theorem dot_origin {n : ℕ} (a : Fin n → ZMod 2) : dot a (origin n) = 0 := by
  simp [dot, origin]

theorem dot_xor {n : ℕ} (a : Fin n → ZMod 2) (x y : Word n) :
    dot a (xor x y) = dot a x + dot a y := by
  simp [dot, AffinePhase.xor, bitValue_xor_two, mul_add, Finset.sum_add_distrib]

@[simp] theorem dot_basis {n : ℕ} (a : Fin n → ZMod 2) (j : Fin n) :
    dot a (basis j) = a j := by
  classical
  simp [dot, basis, bitValue]

/-- Maps from the Boolean group are determined by their values on coordinate words. -/
theorem additive_word_eq {n : ℕ} {A : Type*} [AddCommMonoid A]
    (p q : Word n → A) (hp0 : p (origin n) = 0) (hq0 : q (origin n) = 0)
    (hp : ∀ x y, p (xor x y) = p x + p y)
    (hq : ∀ x y, q (xor x y) = q x + q y)
    (heq : ∀ j, p (basis j) = q (basis j)) : p = q := by
  classical
  have hw (s : Finset (Fin n)) : p (word s) = q (word s) := by
    induction s using Finset.induction_on with
    | empty => simp [hp0, hq0]
    | insert j s hj ih => rw [word_insert s j hj, hp, hq, ih, heq]
  funext x
  let s := Finset.univ.filter (fun j => x j = true)
  have hs : word s = x := by funext j; simp [word, s]
  simpa [hs] using hw s

/-- Every Z/4-valued homomorphism on the Boolean group is an even binary linear form. -/
theorem additive_even_representation {n : ℕ} (p : Word n → ZMod 4)
    (hp0 : p (origin n) = 0) (hp : ∀ x y, p (xor x y) = p x + p y) :
    ∃ a : Fin n → ZMod 2, ∀ x, p x = evenLift (dot a x) := by
  have hcoeff (j : Fin n) : ∃ a : ZMod 2, p (basis j) = evenLift a := by
    have hh := hp (basis j) (basis j)
    rw [AffinePhase.xor_self, hp0] at hh
    generalize he : p (basis j) = t at *
    fin_cases t
    · exact ⟨0, rfl⟩
    · exact False.elim ((by decide : ¬ ((0 : ZMod 4) = 1 + 1)) hh)
    · exact ⟨1, rfl⟩
    · exact False.elim ((by decide : ¬ ((0 : ZMod 4) = 3 + 3)) hh)
  choose a ha using hcoeff
  refine ⟨a, ?_⟩
  have hh : p = fun x => evenLift (dot a x) := additive_word_eq _ _ hp0
    (by simp) hp (by intro x y; rw [dot_xor, evenLift_add]) (by simpa using ha)
  intro x
  exact congrFun hh x

/-- The derivative has no nonconstant odd coefficients, including at arity zero. -/
theorem quadratic_derivative {n : ℕ} (Q : QuadraticPhase n) (w : Word n) :
    ∃ c : ZMod 4, ∃ a : Fin n → ZMod 2, ∀ x,
      Q.eval (xor x w) - Q.eval x = c + evenLift (dot a x) := by
  let d : Word n → ZMod 4 := fun x => Q.eval (xor x w) - Q.eval x
  let p : Word n → ZMod 4 := fun x => d x - d (origin n)
  have hp0 : p (origin n) = 0 := by simp [p]
  have hp (x y : Word n) : p (xor x y) = p x + p y := by
    have hh := quadratic_thirdDifference Q (origin n) x y w
    simp only [thirdDifference, origin_xor] at hh
    dsimp [p, d]
    simp only [origin_xor]
    linear_combination hh
  obtain ⟨a, ha⟩ := additive_even_representation p hp0 hp
  refine ⟨d (origin n), a, ?_⟩
  intro x
  have hh := ha x
  dsimp [p, d] at hh ⊢
  linear_combination hh

end TwoTranslate
end
end Holant.Tractable
