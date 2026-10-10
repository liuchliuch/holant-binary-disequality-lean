import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto

/-! Literal products of unary functions on an equal-coordinate slice. Tables are
indexed by the finite support of a Boolean word; no interaction identity is
assumed in the source hypothesis. -/
namespace Holant.ReedMuller.DiagonalSlice
open scoped BigOperators
variable {α G : Type*} [Fintype α] [DecidableEq α] [CommGroup G]

def outside (i j : α) : Finset α := Finset.univ.erase i |>.erase j

@[simp] theorem mem_outside (i j k : α) : k ∈ outside i j ↔ k ≠ i ∧ k ≠ j := by
  simp [outside, and_comm]

def Simple (h : Finset α → G) (i j : α) : Prop :=
  ∃ a : Bool → G, ∃ b : α → Bool → G, ∀ S : Finset α,
    (i ∈ S ↔ j ∈ S) →
    h S = a (decide (i ∈ S)) * ∏ k ∈ outside i j, b k (decide (k ∈ S))

def NormalizedSimple (h : Finset α → G) (i j : α) : Prop :=
  ∃ a : G, ∃ b : α → G, ∀ S : Finset α,
    (i ∈ S ↔ j ∈ S) →
    h S = (if i ∈ S then a else 1) *
      ∏ k ∈ outside i j, if k ∈ S then b k else 1

theorem normalize {h : Finset α → G} (h0 : h ∅ = 1) {i j : α}
    (hs : Simple h i j) : NormalizedSimple h i j := by
  obtain ⟨a,b,H⟩ := hs
  have H0 := H ∅ (by simp)
  simp only [Finset.notMem_empty, decide_false] at H0
  refine ⟨a true / a false,fun k => b k true / b k false,?_⟩
  intro S hS
  have ha : a (decide (i ∈ S)) / a false = (if i ∈ S then a true/a false else 1) := by
    by_cases hi : i ∈ S <;> simp [hi]
  have hb (k : α) : b k (decide (k ∈ S)) / b k false =
      (if k ∈ S then b k true/b k false else 1) := by
    by_cases hk : k ∈ S <;> simp [hk]
  calc
    h S = h S / h ∅ := by rw [h0,div_one]
    _ = (a (decide (i ∈ S)) / a false) *
        ∏ k ∈ outside i j, b k (decide (k ∈ S)) / b k false := by
      rw [H S hS,H0,Finset.prod_div_distrib]
      exact mul_div_mul_comm _ _ _ _
    _ = _ := by simp only [ha,hb]

theorem normalized_simple {h : Finset α → G} {i j : α}
    (hs : NormalizedSimple h i j) : Simple h i j := by
  obtain ⟨a,b,H⟩ := hs
  refine ⟨(fun t => if t then a else 1),(fun k t => if t then b k else 1),?_⟩
  intro S hS
  simpa using H S hS

 theorem prod_indicator (U S : Finset α) (f : α → G) :
    (∏ k ∈ U, if k ∈ S then f k else 1) = ∏ k ∈ U ∩ S, f k := by
  rw [←Finset.prod_filter]
  congr 1

theorem slice_formula {h : Finset α → G} (h0 : h ∅ = 1) {i j : α} (hij : i ≠ j)
    (hs : Simple h i j) (S : Finset α) (hS : i ∈ S ↔ j ∈ S) :
    h S = (if i ∈ S then h {i,j} else 1) *
      ∏ k ∈ outside i j ∩ S, h {k} := by
  obtain ⟨a,b,H⟩ := normalize h0 hs
  have hp : h {i,j} = a := by
    rw [H _ (by simp),if_pos (by simp)]
    have hz : outside i j ∩ {i,j} = ∅ := by ext k; simp
    rw [prod_indicator,hz,Finset.prod_empty,mul_one]
  have hk (k : α) (hi : k ≠ i) (hj : k ≠ j) : h {k} = b k := by
    rw [H _ (by simp [Ne.symm hi,Ne.symm hj]),if_neg (by simp [Ne.symm hi]),one_mul]
    rw [prod_indicator]
    have hz : outside i j ∩ {k} = {k} := by ext l; simp; aesop
    rw [hz,Finset.prod_singleton]
  rw [H S hS,prod_indicator,hp]
  congr 1
  apply Finset.prod_congr rfl
  intro k hkS
  obtain ⟨hi,hj⟩ := (mem_outside i j k).mp (Finset.mem_inter.mp hkS).1
  exact (hk k hi hj).symm

end Holant.ReedMuller.DiagonalSlice
