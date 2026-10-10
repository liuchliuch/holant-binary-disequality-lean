import Holant.Proofs.LinearProgramming.Interface
import Mathlib.Algebra.BigOperators.Fin

/-!
Exact finite averaging for the original bounded rational system.

The operations below are rational sums, division by a positive natural, and
literal list construction. The semantic lemmas do not assume an LP solver.
The final maximality lemma states its finite-family coverage premise openly;
this file does not claim to produce such a family or an LP machine.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Average
open Holant.LocalDrafts.TraversalCompletion.RationalLP.Codec
open scoped BigOperators

/-- The extra base slot makes the average defined even in dimension zero. -/
def value (d : Raw) (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ)
    (j : Fin d.dimension) : ℚ :=
  (∑ i, samples i j) / (d.dimension + 1 : ℕ)

def list (d : Raw) (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ) : List ℚ :=
  List.ofFn (value d samples)

@[simp] theorem length (d : Raw) (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ) :
    (list d samples).length = d.dimension := by simp [list]

@[simp] theorem point_list (d : Raw)
    (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ) :
    point d (list d samples) = value d samples := by
  funext j
  simp [list, point, List.getD_eq_getElem]

theorem feasible (d : Raw) (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ)
    (hf : ∀ i, Feasible d (samples i)) : Feasible d (value d samples) := by
  have hm : (0 : ℚ) < (d.dimension + 1 : ℕ) := by positivity
  constructor
  · intro row
    calc
      (∑ j, (d.coefficient row j : ℚ) * value d samples j) =
          (∑ j, ∑ i, (d.coefficient row j : ℚ) * samples i j) / (d.dimension + 1 : ℕ) := by
        simp only [value, mul_div_assoc, Finset.mul_sum, Finset.sum_div]
      _ = (∑ i, ∑ j, (d.coefficient row j : ℚ) * samples i j) / (d.dimension + 1 : ℕ) := by
        rw [Finset.sum_comm]
      _ = (∑ _i : Fin (d.dimension + 1), (d.constant row : ℚ)) / (d.dimension + 1 : ℕ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact (hf i).1 row
      _ = d.constant row := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [ne_of_gt hm] <;> ring
  · intro j
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun i _ => ((hf i).2 j).1)) hm.le
    · apply (div_le_iff₀ hm).mpr
      calc
        (∑ i, samples i j) ≤ ∑ _i : Fin (d.dimension + 1), (1 : ℚ) :=
          Finset.sum_le_sum (fun i _ => ((hf i).2 j).2)
        _ = _ := by simp

theorem solution (d : Raw) (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ)
    (hf : ∀ i, Feasible d (samples i)) : Solution d (list d samples) := by
  exact ⟨length d samples, by simpa only [point_list] using feasible d samples hf⟩

theorem positive_of_member (d : Raw)
    (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ)
    (hf : ∀ i, Feasible d (samples i)) (i : Fin (d.dimension + 1))
    (j : Fin d.dimension) (hp : 0 < samples i j) : 0 < value d samples j := by
  have hu : samples i j ≤ ∑ k, samples k j :=
    Finset.single_le_sum (fun k _ => ((hf k).2 j).1) (Finset.mem_univ i)
  exact div_pos (hp.trans_le hu) (by positivity)

/-- A feasible average has no positive coordinate outside the union of the
feasible supports; covering each possible positive coordinate suffices. -/
theorem maximal_support (d : Raw)
    (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ)
    (hf : ∀ i, Feasible d (samples i))
    (hc : ∀ j, Positive d j → ∃ i, 0 < samples i j) (j : Fin d.dimension) :
    0 < point d (list d samples) j ↔ Positive d j := by
  rw [point_list]
  constructor
  · intro hp
    exact ⟨value d samples, feasible d samples hf, hp⟩
  · intro hp
    obtain ⟨i, hi⟩ := hc j hp
    exact positive_of_member d samples hf i j hi

theorem zero_iff (d : Raw)
    (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ)
    (hf : ∀ i, Feasible d (samples i))
    (hc : ∀ j, Positive d j → ∃ i, 0 < samples i j) (j : Fin d.dimension) :
    point d (list d samples) j = 0 ↔ ¬ Positive d j := by
  have hnonneg := ((solution d samples hf).2.2 j).1
  have hpos := maximal_support d samples hf hc j
  constructor
  · intro hz hp
    have h := hpos.mpr hp
    simpa only [hz, lt_self_iff_false] using h
  · intro hn
    exact le_antisymm (le_of_not_gt (fun hp => hn (hpos.mp hp))) hnonneg

/-- Every fallback uses the actual same base point; the base occurs as the
last member even if every coordinate query fails. -/
def selected (d : Raw) (base : List ℚ)
    (columns : Fin d.dimension → Option (List ℚ)) :
    Fin (d.dimension + 1) → Fin d.dimension → ℚ :=
  Fin.lastCases (point d base) (fun j => point d ((columns j).getD base))

theorem selected_feasible (d : Raw) (base : List ℚ)
    (columns : Fin d.dimension → Option (List ℚ)) (hb : Solution d base)
    (hs : ∀ j xs, columns j = some xs → Feasible d (point d xs))
    (i : Fin (d.dimension + 1)) : Feasible d (selected d base columns i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [selected, Fin.lastCases_last] using hb.2
  · cases he : columns j with
    | none => simpa only [selected, Fin.lastCases_castSucc, he, Option.getD_none] using hb.2
    | some xs =>
      simpa only [selected, Fin.lastCases_castSucc, he, Option.getD_some] using hs j xs he

theorem selected_maximal (d : Raw) (base : List ℚ)
    (columns : Fin d.dimension → Option (List ℚ)) (hb : Solution d base)
    (hs : ∀ j xs, columns j = some xs → Feasible d (point d xs) ∧ 0 < point d xs j)
    (hc : ∀ j, Positive d j → ∃ xs, columns j = some xs)
    (j : Fin d.dimension) :
    0 < point d (list d (selected d base columns)) j ↔ Positive d j := by
  apply maximal_support d (selected d base columns)
    (selected_feasible d base columns hb (fun j xs h => (hs j xs h).1))
  intro k hp
  obtain ⟨xs, hx⟩ := hc k hp
  exact ⟨k.castSucc, by
    simpa only [selected, Fin.lastCases_castSucc, hx, Option.getD_some] using (hs k xs hx).2⟩

@[simp] theorem list_zero_dimension (d : Raw) (hn : d.dimension = 0)
    (samples : Fin (d.dimension + 1) → Fin d.dimension → ℚ) : list d samples = [] := by
  apply List.eq_nil_iff_length_eq_zero.mpr
  simpa only [length] using hn

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Average
