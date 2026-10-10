import Holant.Proofs.LinearProgramming.Interface

/-! Direct one-dimensional rational feasibility, without affine-chart machinery.
The first nonzero coefficient determines the only possible scalar; if every
coefficient is zero, the scalar one realizes maximal possible support.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.LowDimension.OneDim
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open scoped BigOperators

def pick : List (ℤ × ℤ) → Option ℚ
  | [] => none
  | (a,b) :: rest => if a = 0 then pick rest else some ((b : ℚ) / (a : ℚ))

theorem pick_none (rs : List (ℤ × ℤ)) :
    pick rs = none ↔ ∀ r ∈ rs, r.1 = 0 := by
  induction rs with
  | nil => simp [pick]
  | cons r rs ih =>
    rcases r with ⟨a,b⟩
    by_cases ha : a = 0 <;> simp [pick, ha, ih]

theorem pick_some (rs : List (ℤ × ℤ)) (x t : ℚ)
    (h : ∀ r ∈ rs, (r.1 : ℚ) * x = (r.2 : ℚ))
    (hp : pick rs = some t) : x = t := by
  induction rs with
  | nil => simp [pick] at hp
  | cons r rs ih =>
    rcases r with ⟨a,b⟩
    by_cases ha : a = 0
    · apply ih (fun r hr => h r (by simp [hr]))
      simpa [pick, ha] using hp
    · have ht : (b : ℚ) / (a : ℚ) = t := by simpa [pick, ha] using hp
      rw [← ht]
      apply (eq_div_iff (by exact_mod_cast ha)).2
      simpa [mul_comm] using h (a,b) (by simp)

def rows (d : Codec.Raw) : List (ℤ × ℤ) :=
  (List.range d.rowCount).map fun i => ((d.rows.getD i []).getD 0 0, d.rhs.getD i 0)
def candidate (d : Codec.Raw) : ℚ := (pick (rows d)).getD 1

def accepted (d : Codec.Raw) : Bool :=
  decide (0 ≤ candidate d ∧ candidate d ≤ 1) &&
    (rows d).all (fun r => decide ((r.1 : ℚ) * candidate d = (r.2 : ℚ)))
def value (d : Codec.Raw) : Option (List ℚ) :=
  if accepted d then some [candidate d] else none

theorem rows_condition (d : Codec.Raw) (hn : d.dimension = 1) (x : ℚ) :
    (∀ r ∈ rows d, (r.1 : ℚ) * x = (r.2 : ℚ)) ↔
    ∀ i : Fin d.rowCount, ∑ j : Fin d.dimension,
      (d.coefficient i j : ℚ) * x = d.constant i := by
  have sum_one (i : Fin d.rowCount) :
      (∑ j : Fin d.dimension, (d.coefficient i j : ℚ) * x) =
        ((d.rows.getD i.val []).getD 0 0 : ℚ) * x := by
    let j0 : Fin d.dimension := ⟨0, by omega⟩
    rw [Finset.sum_eq_single j0]
    · rfl
    · intro j _ hne
      exfalso; apply hne; apply Fin.ext
      have hj := j.isLt
      dsimp [j0]; omega
    · simp
  simp only [rows, List.mem_map, List.mem_range]
  simp only [sum_one, Codec.Raw.constant]
  constructor
  · intro h i
    have hi := h _ ⟨i.val, i.isLt, rfl⟩
    exact hi
  · intro h r hr
    obtain ⟨i,hi,rfl⟩ := hr
    exact h ⟨i,hi⟩

theorem accepted_iff (d : Codec.Raw) (hn : d.dimension = 1) :
    accepted d = true ↔ Codec.Feasible d (fun _ => candidate d) := by
  rw [accepted, Bool.and_eq_true, decide_eq_true_eq]
  simp only [List.all_eq_true, decide_eq_true_eq]
  rw [rows_condition d hn]
  constructor
  · rintro ⟨hb,he⟩; exact ⟨he,fun _ => hb⟩
  · rintro ⟨he,hb⟩
    exact ⟨hb ⟨0,by omega⟩,he⟩

/-- Feasibility of any scalar forces feasibility of the computed candidate. -/
theorem candidate_complete (d : Codec.Raw) (hn : d.dimension = 1)
    (x : Fin d.dimension → ℚ) (hx : Codec.Feasible d x) :
    Codec.Feasible d (fun _ => candidate d) := by
  let j : Fin d.dimension := ⟨0,by omega⟩
  have hsame : ∀ k : Fin d.dimension, k = j := by
    intro k; apply Fin.ext; have hk := k.isLt; dsimp [j]; omega
  have hr : ∀ r ∈ rows d, (r.1 : ℚ) * x j = (r.2 : ℚ) := by
    apply (rows_condition d hn (x j)).2
    intro i
    simpa only [hsame] using hx.1 i
  cases hp : pick (rows d) with
  | some t =>
    have ht := pick_some (rows d) (x j) t hr hp
    have hc : candidate d = x j := by simp [candidate,hp,ht]
    constructor
    · intro i; simpa only [hc,hsame] using hx.1 i
    · intro k; simpa only [hc] using hx.2 j
  | none =>
    have hz := (pick_none (rows d)).1 hp
    have hc : candidate d = 1 := by simp [candidate,hp]
    constructor
    · apply (rows_condition d hn (candidate d)).1
      intro r hmem
      have hb := hr r hmem
      rw [hz r hmem] at hb ⊢
      simpa using hb
    · intro k; simp [hc]

theorem none_iff (d : Codec.Raw) (hn : d.dimension = 1) :
    value d = none ↔ ¬ ∃ x, Codec.Feasible d x := by
  have he : (∃ x, Codec.Feasible d x) ↔ accepted d = true := by
    constructor
    · rintro ⟨x,hx⟩
      exact (accepted_iff d hn).2 (candidate_complete d hn x hx)
    · intro h; exact ⟨_,(accepted_iff d hn).1 h⟩
  rw [he]
  cases h : accepted d <;> simp [value,h]

theorem response (d : Codec.Raw) (hn : d.dimension = 1) :
    Codec.Response d (value d) := by
  cases h : accepted d
  · simpa [value,h,Codec.Response] using (none_iff d hn).1 (by simp [value,h])
  · have hf := (accepted_iff d hn).1 h
    simp only [value,h,↓reduceIte,Codec.Response,Codec.Solution]
    refine ⟨by simp [hn], ?_⟩
    have he : Codec.point d [candidate d] = fun _ => candidate d := by
      funext j
      have hj : j.val = 0 := by have hj := j.isLt; omega
      simp [Codec.point,hj]
    rw [he]; exact hf

/-- The chosen scalar realizes every feasible positive coordinate. -/
theorem maximalSupport (d : Codec.Input) (hn : d.val.dimension = 1)
    (xs : List ℚ) (hv : value d.val = some xs) :
    ∀ j : Fin d.val.dimension, 0 < Codec.point d.val xs j ↔
      Holant.LocalDrafts.RemoteWork.RationalLP.PositiveAt d j := by
  have hs : Codec.Solution d.val xs := by
    have h := response d.val hn
    rw [hv] at h
    exact h
  have hx : xs = [candidate d.val] := by
    unfold value at hv
    split at hv
    · simpa using hv.symm
    · simp at hv
  intro j
  constructor
  · intro hj
    exact ⟨Codec.point d.val xs, hs.2, hj⟩
  · rintro ⟨y,hy,hj⟩
    have hj0 : j.val = 0 := by have h := j.isLt; omega
    rw [hx]
    simp only [Codec.point,hj0,List.getD_cons_zero]
    have same : ∀ k : Fin d.val.dimension, k = j := by
      intro k; apply Fin.ext; have hk := k.isLt; omega
    have hr : ∀ r ∈ rows d.val, (r.1 : ℚ) * y j = (r.2 : ℚ) := by
      apply (rows_condition d.val hn (y j)).2
      intro i
      simpa only [same] using hy.1 i
    cases hp : pick (rows d.val) with
    | none => simp [candidate,hp]
    | some t =>
      have ht := pick_some (rows d.val) (y j) t hr hp
      simpa [candidate,hp,← ht] using hj

end Holant.LocalDrafts.RemoteWork.RationalLP.LowDimension.OneDim
