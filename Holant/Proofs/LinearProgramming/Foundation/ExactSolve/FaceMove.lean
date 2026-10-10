import Holant.Proofs.LinearProgramming.Foundation.InputBounds
import Mathlib.Data.Finset.Max

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Rational motion to the first box boundary. Every old tight coordinate remains
tight; one previously interior coordinate becomes tight. No optimal point,
active basis or positive step length is assumed. These are semantic existence
lemmas, not a polynomial pivot algorithm.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.FaceMove
open Codec
open scoped BigOperators

def Tight {n : ℕ} (x : Fin n → ℚ) (k : Fin n) : Prop := x k = 0 ∨ x k = 1
def tightSet {n : ℕ} (x : Fin n → ℚ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => x k = 0 ∨ x k = 1)

@[simp] theorem mem_tightSet {n : ℕ} (x : Fin n → ℚ) (k : Fin n) :
    k ∈ tightSet x ↔ Tight x k := by simp [tightSet, Tight]

def Tangent (d : Raw) (x v : Fin d.dimension → ℚ) : Prop :=
  (∀ i, ∑ k, (d.coefficient i k : ℚ) * v k = 0) ∧
    ∀ k, Tight x k → v k = 0

def Rigid (d : Raw) (x : Fin d.dimension → ℚ) : Prop :=
  ∀ v, Tangent d x v → v = 0

def move {n : ℕ} (x v : Fin n → ℚ) (t : ℚ) : Fin n → ℚ := fun k => x k + t*v k
def hitTime {n : ℕ} (x v : Fin n → ℚ) (k : Fin n) : ℚ :=
  if 0 < v k then (1-x k)/v k else -x k/v k

theorem interior (d : Raw) (x v : Fin d.dimension → ℚ) (hx : Feasible d x)
    (hv : Tangent d x v) (k : Fin d.dimension) (hk : v k ≠ 0) : 0 < x k ∧ x k < 1 := by
  have h0 : x k ≠ 0 := fun h => hk (hv.2 k (Or.inl h))
  have h1 : x k ≠ 1 := fun h => hk (hv.2 k (Or.inr h))
  exact ⟨lt_of_le_of_ne (hx.2 k).1 h0.symm, lt_of_le_of_ne (hx.2 k).2 h1⟩

theorem hitTime_pos (d : Raw) (x v : Fin d.dimension → ℚ) (hx : Feasible d x)
    (hv : Tangent d x v) (k : Fin d.dimension) (hk : v k ≠ 0) : 0 < hitTime x v k := by
  have hi := interior d x v hx hv k hk
  by_cases hp : 0 < v k
  · simpa [hitTime,hp] using div_pos (sub_pos.mpr hi.2) hp
  · have hn : v k < 0 := lt_of_le_of_ne (le_of_not_gt hp) hk
    simpa [hitTime, hp] using div_pos_of_neg_of_neg (neg_neg_of_pos hi.1) hn

theorem coordinate_box {n : ℕ} (x v : Fin n → ℚ) (k : Fin n)
    (hx : 0 ≤ x k ∧ x k ≤ 1) (t : ℚ) (ht : 0 ≤ t)
    (hb : v k ≠ 0 → t ≤ hitTime x v k) : 0 ≤ move x v t k ∧ move x v t k ≤ 1 := by
  by_cases hz : v k = 0
  · simpa [move, hz] using hx
  · by_cases hp : 0 < v k
    · have hh := (le_div_iff₀ hp).mp (by simpa [hitTime, hp] using hb hz)
      have hn := mul_nonneg ht hp.le
      constructor <;> dsimp [move] <;> linarith
    · have hn : v k < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
      have hh := (le_div_iff_of_neg hn).mp (by simpa [hitTime, hp] using hb hz)
      have hm := mul_nonpos_of_nonneg_of_nonpos ht hn.le
      constructor <;> dsimp [move] <;> linarith

theorem hits_boundary {n : ℕ} (x v : Fin n → ℚ) (k : Fin n) (hk : v k ≠ 0) :
    Tight (move x v (hitTime x v k)) k := by
  by_cases hp : 0 < v k
  · right
    simp only [move, hitTime, hp, ↓reduceIte, div_mul_cancel₀ _ hk]
    ring
  · left
    simp only [move, hitTime, hp, ↓reduceIte, div_mul_cancel₀ _ hk]
    ring

theorem move_equations (d : Raw) (x v : Fin d.dimension → ℚ) (hx : Feasible d x)
    (hv : Tangent d x v) (t : ℚ) (i : Fin d.rowCount) :
    ∑ k, (d.coefficient i k : ℚ)*move x v t k = d.constant i := by
  calc
    _ = (∑ k, (d.coefficient i k : ℚ)*x k) + t*(∑ k, (d.coefficient i k : ℚ)*v k) := by
      simp only [move, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hx.1 i, hv.1 i]; ring

theorem old_tight (d : Raw) (x v : Fin d.dimension → ℚ) (hv : Tangent d x v)
    (t : ℚ) : tightSet x ⊆ tightSet (move x v t) := by
  intro k hk
  have h := (mem_tightSet x k).mp hk
  have hz := hv.2 k h
  apply (mem_tightSet (move x v t) k).mpr
  have he : move x v t k = x k := by
    simp only [move, hz, mul_zero, add_zero]
  simpa only [Tight, he] using h

theorem orient (d : Raw) (x v : Fin d.dimension → ℚ) (hv : Tangent d x v)
    (hn : v ≠ 0) (j : Fin d.dimension) :
    ∃ w, Tangent d x w ∧ w ≠ 0 ∧ 0 ≤ w j := by
  by_cases hj : 0 ≤ v j
  · exact ⟨v,hv,hn,hj⟩
  · refine ⟨-v,⟨?_,?_⟩,neg_ne_zero.mpr hn,by simpa using neg_nonneg.mpr (le_of_not_ge hj)⟩
    · intro i
      simpa [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] using congrArg Neg.neg (hv.1 i)
    · intro k hk
      simp [hv.2 k hk]

/-- The minimizing coordinate and strictly positive step are derived from v. -/
theorem first_boundary (d : Raw) (x v : Fin d.dimension → ℚ) (hx : Feasible d x)
    (hv : Tangent d x v) (hn : v ≠ 0) :
    ∃ t k, 0 < t ∧ v k ≠ 0 ∧ Feasible d (move x v t) ∧
      Tight (move x v t) k ∧ ¬ Tight x k ∧
      tightSet x ⊂ tightSet (move x v t) := by
  classical
  have hsome : ∃ k, v k ≠ 0 := by
    by_contra h
    apply hn
    funext k
    simpa using not_exists.mp h k
  let s := Finset.univ.filter (fun k => v k ≠ 0)
  have hs : s.Nonempty := by obtain ⟨k,hk⟩ := hsome; exact ⟨k,by simp [s,hk]⟩
  obtain ⟨k,hk,hmin⟩ := s.exists_min_image (hitTime x v) hs
  have hk0 : v k ≠ 0 := by simpa [s] using hk
  let t := hitTime x v k
  have ht : 0 < t := hitTime_pos d x v hx hv k hk0
  have hbox : ∀ l, 0 ≤ move x v t l ∧ move x v t l ≤ 1 := by
    intro l
    exact coordinate_box x v l (hx.2 l) t ht.le (fun hl => hmin l (by simp [s,hl]))
  have hhit : Tight (move x v t) k := hits_boundary x v k hk0
  have hnot : ¬ Tight x k := fun h => hk0 (hv.2 k h)
  refine ⟨t,k,ht,hk0,⟨move_equations d x v hx hv t,hbox⟩,hhit,hnot,?_⟩
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨old_tight d x v hv t,?_⟩
  intro he
  apply hnot
  apply (mem_tightSet x k).mp
  rw [he]
  exact (mem_tightSet _ k).mpr hhit

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.FaceMove
