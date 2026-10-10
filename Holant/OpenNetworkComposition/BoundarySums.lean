import Holant.OpenNetworkComposition.Semantics
import Mathlib.Tactic.FinCases

/-! Original-boundary assignment filters for one disjoint connection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition
namespace FiniteShape
variable {V F E : Type*} {n : ℕ}

def awayAgrees (s : FiniteShape V F E n) (i : Fin n) (z : Ports V F s.arity → Bool) (x : Fin n → Bool) : Prop :=
  ∀ j,j≠i → z (s.boundary j)=x j

theorem boundary_update_iff (s : FiniteShape V F E n) (i : Fin n)
    (z : Ports V F s.arity → Bool) (x : Fin n → Bool) (a : Bool) :
    (∀j,z (s.boundary j)=Function.update x i a j) ↔
      z (s.boundary i)=a ∧ s.awayAgrees i z x := by
  constructor
  · intro h
    exact ⟨by simpa using h i,fun j hj => by simpa [Function.update_of_ne hj] using h j⟩
  · rintro ⟨hi,h⟩ j
    by_cases hj : j=i
    · subst j; simpa using hi
    · simpa [Function.update_of_ne hj] using h j hj

theorem boundary_binary_iff (s : FiniteShape V F E 2) (z : Ports V F s.arity → Bool) (u b : Bool) :
    (∀j,z (s.boundary j)=(![u,b] : Fin 2 → Bool) j) ↔ z (s.boundary 0)=u ∧ z (s.boundary 1)=b := by
  constructor
  · intro h; exact ⟨h 0,h 1⟩
  · rintro ⟨h0,h1⟩ j
    fin_cases j
    · exact h0
    · exact h1

end FiniteShape

variable {K : Type*} [CommSemiring K]

/-- Explicit transport between extensionally identical finite enumerations. -/
theorem sum_instances {A : Type*} (I J : Fintype A) (f g : A → K) (h : ∀a,f a=g a) :
    (@Finset.univ A I).sum f=(@Finset.univ A J).sum g := by
  have he : I=J := Subsingleton.elim _ _
  cases he
  exact Finset.sum_congr rfl (fun a _ => h a)

theorem sum_four_swap {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (g : A → B → C → D → K) :
    (∑a,∑b,∑c,∑d,g a b c d)=∑c,∑d,∑a,∑b,g a b c d := by
  calc
    _ = ∑a,∑c,∑b,∑d,g a b c d := by apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
    _ = ∑c,∑a,∑b,∑d,g a b c d := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      calc
        _ = ∑a,∑d,∑b,g a b c d := by apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

theorem sum_three_swap {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (g : A → B → C → K) : (∑a,∑b,∑c,g a b c)=∑b,∑c,∑a,g a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

/-- The exact single-connection tensor, with only one shared native edge. -/
def spliceTensor {n : ℕ} (L : Signature K n) (R : Signature K 2) (i : Fin n) : Signature K n :=
  fun x => ∑ a : Bool,∑ b : Bool,L (Function.update x i a)*R (![x i,b])*Signature.disequality a b

end Holant.OpenNetworkComposition
