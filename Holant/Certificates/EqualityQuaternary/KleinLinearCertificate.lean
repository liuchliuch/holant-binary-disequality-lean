import Holant.Certificates.EqualityQuaternary.KleinBasis

/-! Exact finite row-span certificates for unions of safe linear planes.
Every computed row identity is checked in Lean; soundness quantifies over
arbitrary algebraic coefficients and admits every zero-card branch.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein.Linear
open Holant.Marked

abbrev Row := Fin 4 → Q
abbrev Weights := List (ℕ × Q)
def evaluate (r : Row) (c : Fin 4 → Scalar) : Scalar := ∑ i,embed (r i)*c i
def Satisfies (rows : List Row) (c : Fin 4 → Scalar) : Prop := ∀ r∈rows,evaluate r c=0

def combine (rows : List Row) : Weights → Row
  | [] => fun _ => 0
  | (j,a)::rest => fun i => a*(rows.getD j (fun _ => 0)) i+combine rows rest i

theorem satisfies_getD {rows : List Row} {c : Fin 4 → Scalar} (h : Satisfies rows c) (j : ℕ) :
    evaluate (rows.getD j (fun _ => 0)) c=0 := by
  by_cases hj : j<rows.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [evaluate]

theorem evaluate_combine {rows : List Row} {c : Fin 4 → Scalar}
    (h : Satisfies rows c) (w : Weights) : evaluate (combine rows w) c=0 := by
  induction w with
  | nil => simp [combine,evaluate]
  | cons ja rest ih =>
    rcases ja with ⟨j,a⟩
    have he : evaluate (combine rows ((j,a)::rest)) c =
        embed a*evaluate (rows.getD j (fun _ => 0)) c+evaluate (combine rows rest) c := by
      simp only [combine,evaluate,map_add,map_mul,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he,satisfies_getD h j,ih,mul_zero,add_zero]

def checkRow (rows : List Row) (r : Row) (w : Weights) : Bool := decide (r=combine rows w)
theorem checked_row {rows : List Row} {r : Row} {w : Weights}
    (hc : checkRow rows r w=true) {c : Fin 4 → Scalar} (h : Satisfies rows c) : evaluate r c=0 := by
  have he : r=combine rows w := of_decide_eq_true hc
  rw [he]
  exact evaluate_combine h w

def checkRows (old new : List Row) (w : Fin new.length → Weights) : Bool :=
  decide (∀ i : Fin new.length,checkRow old (new.get i) (w i)=true)

theorem checked_rows (old new : List Row) (w : Fin new.length → Weights)
    (hc : checkRows old new w=true) {c : Fin 4 → Scalar} (h : Satisfies old c) : Satisfies new c := by
  have hall : ∀ i : Fin new.length,checkRow old (new.get i) (w i)=true := of_decide_eq_true hc
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact checked_row (hall i) h

structure Problem (t : ℕ) where
  cards : Fin 16 → Fin 4 → Row
  targets : Fin t → List Row

def Problem.Safe {t : ℕ} (p : Problem t) (c : Fin 4 → Scalar) : Prop :=
  ∀ k,∃ axis : Fin 4,∀ i,i≠axis → evaluate (p.cards k i) c=0
def Problem.Accepted {t : ℕ} (p : Problem t) (c : Fin 4 → Scalar) : Prop :=
  ∃ i,Satisfies (p.targets i) c
def Covers {t : ℕ} (p : Problem t) (rows : List Row) : Prop :=
  ∀ c,Satisfies rows c → p.Safe c → p.Accepted c

def axisRows (cards : Fin 4 → Row) (axis : Fin 4) : List Row :=
  List.ofFn (fun i => if i=axis then (fun _ => 0) else cards i)

theorem axis_satisfied (cards : Fin 4 → Row) (axis : Fin 4) (c : Fin 4 → Scalar)
    (h : ∀ i,i≠axis → evaluate (cards i) c=0) : Satisfies (axisRows cards axis) c := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  by_cases hi : i=axis
  · simp [hi,evaluate]
  · simpa [hi] using h i hi

theorem covers_target {t : ℕ} (p : Problem t) (rows : List Row) (j : Fin t)
    (w : Fin (p.targets j).length → Weights) (hc : checkRows rows (p.targets j) w=true) : Covers p rows := by
  intro c hr _
  exact ⟨j,checked_rows rows _ w hc hr⟩

theorem covers_split {t : ℕ} (p : Problem t) (rows : List Row) (context : Fin 16)
    (reduced : Fin 4 → List Row)
    (w : (a : Fin 4) → Fin (reduced a).length → Weights)
    (hc : ∀ a,checkRows (rows++axisRows (p.cards context) a) (reduced a) (w a)=true)
    (children : ∀ a,Covers p (reduced a)) : Covers p rows := by
  intro c hr hs
  obtain ⟨a,ha⟩ := hs context
  have hnew : Satisfies (rows++axisRows (p.cards context) a) c := by
    intro r hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hr r hh
    · exact axis_satisfied _ a c ha r hh
  exact children a c (checked_rows _ _ (w a) (hc a) hnew) hs

end Holant.Certificates.EqualityQuaternary.Klein.Linear
