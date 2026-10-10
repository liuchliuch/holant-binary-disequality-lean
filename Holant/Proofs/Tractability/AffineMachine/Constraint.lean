import Holant.Proofs.Tractability.AffineMachine.Model


namespace Holant.LocalDrafts.Tractability.AffineMachine.Constraint

open Holant.Tractable AffinePhase TwoTranslate
open scoped BigOperators

def first {A : Type} (test : A → Bool) : List A → Option A
  | [] => none
  | a :: as => if test a then some a else first test as

theorem first_some {A : Type} (test : A → Bool) (xs : List A) (a : A)
    (h : first test xs = some a) : a ∈ xs ∧ test a = true := by
  induction xs with
  | nil => simp [first] at h
  | cons b bs ih =>
    cases hb : test b <;> simp [first, hb] at h
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩
    · subst a; exact ⟨by simp, hb⟩

theorem first_none {A : Type} (test : A → Bool) (xs : List A) :
    first test xs = none ↔ ∀ a ∈ xs, test a = false := by
  induction xs with
  | nil => simp [first]
  | cons a as ih => cases h : test a <;> simp [first, h, ih]

def positions {n : ℕ} (S : AffineSystem n) : List (Fin S.rows × Fin n) :=
  (List.finRange S.rows).flatMap (fun r => (List.finRange n).map (fun j => (r, j)))

def pivot {n : ℕ} (S : AffineSystem n) : Option (Fin S.rows × Fin n) :=
  first (fun p => decide (S.matrix p.1 p.2 ≠ 0)) (positions S)

theorem position_mem {n : ℕ} (S : AffineSystem n) (r : Fin S.rows) (j : Fin n) :
    (r, j) ∈ positions S := by simp [positions]

theorem pivot_some {n : ℕ} (S : AffineSystem n) (r : Fin S.rows) (j : Fin n)
    (h : pivot S = some (r, j)) : S.matrix r j = 1 := by
  have hn : S.matrix r j ≠ 0 := of_decide_eq_true (first_some _ _ _ h).2
  exact (binary_cases (S.matrix r j)).resolve_left hn

theorem pivot_none {n : ℕ} (S : AffineSystem n) (h : pivot S = none) :
    ∀ r j, S.matrix r j = 0 := by
  intro r j
  have hz := (first_none _ _).mp h (r, j) (position_mem S r j)
  simpa using hz

/-- Only rows and their explicit columns are inspected. -/
def badRow {n : ℕ} (S : AffineSystem n) : Bool :=
  (List.finRange S.rows).any (fun r =>
    ((List.finRange n).all (fun j => decide (S.matrix r j = 0))) && decide (S.rhs r ≠ 0))

theorem badRow_spec {n : ℕ} (S : AffineSystem n) :
    badRow S = true ↔ ∃ r, (∀ j, S.matrix r j = 0) ∧ S.rhs r ≠ 0 := by
  simp [badRow, List.any_eq_true, List.all_eq_true]

theorem badRow_no_solution {n : ℕ} (S : AffineSystem n) (h : badRow S = true) (x : Word n) :
    ¬ S.Holds x := by
  obtain ⟨r, hr, hb⟩ := (badRow_spec S).mp h
  intro hx
  have hh := hx r
  simp only [hr, zero_mul, Finset.sum_const_zero] at hh
  exact hb hh.symm

theorem no_pivot_holds {n : ℕ} (S : AffineSystem n) (hp : pivot S = none)
    (hb : badRow S = false) (x : Word n) : S.Holds x := by
  have hm := pivot_none S hp
  intro r
  have hr : S.rhs r = 0 := by
    by_contra hn
    have h := (badRow_spec S).mpr ⟨r, hm r, hn⟩
    simp [hb] at h
  simp [hm, hr]

def tailRow {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1)) : Fin n → ZMod 2 :=
  fun k => S.matrix r (Equiv.swap 0 j k.succ)

noncomputable def selectedBit {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1)) (x : Word n) : Bool :=
  residueBit (S.rhs r - dot (tailRow S r j) x)

noncomputable def solveMap {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1)) (x : Word n) : Word (n + 1) :=
  permute j (Fin.cons (selectedBit S r j x) x)

theorem selectedBit_affine {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1))
    (x y : Word n) : selectedBit S r j (xor x y) =
      Bool.xor (selectedBit S r j x) (Bool.xor (selectedBit S r j y) (selectedBit S r j (origin n))) := by
  apply bitValue_injective
  simp only [selectedBit, bitValue_xor_two, bitValue_residueBit, dot_xor, dot_origin, sub_zero]
  ring_nf
  have h3 : (3 : ZMod 2) = 1 := by decide
  simp [h3]

theorem solveMap_affine {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1)) :
    IsAffineMap (solveMap S r j) := by
  intro x y
  funext i
  change Fin.cons (α := fun _ : Fin (n + 1) => Bool)
      (selectedBit S r j (xor x y)) (xor x y) (Equiv.swap (0 : Fin (n + 1)) j i) =
    Bool.xor (Fin.cons (α := fun _ : Fin (n + 1) => Bool)
      (selectedBit S r j x) x (Equiv.swap (0 : Fin (n + 1)) j i))
      (Bool.xor (Fin.cons (α := fun _ : Fin (n + 1) => Bool)
        (selectedBit S r j y) y (Equiv.swap (0 : Fin (n + 1)) j i))
        (Fin.cons (α := fun _ : Fin (n + 1) => Bool)
          (selectedBit S r j (origin n)) (origin n) (Equiv.swap (0 : Fin (n + 1)) j i)))
  generalize Equiv.swap (0 : Fin (n + 1)) j i = k
  refine Fin.cases ?_ (fun k => ?_) k
  · exact selectedBit_affine S r j x y
  · simp [AffinePhase.xor, origin]

theorem selected_row {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1))
    (hj : S.matrix r j = 1) (bit : Bool) (x : Word n) :
    rowDot (S.matrix r) (permute j (Fin.cons bit x)) =
      bitValue (ZMod 2) bit + dot (tailRow S r j) x := by
  have hs := Equiv.sum_comp (Equiv.swap (0 : Fin (n + 1)) j)
    (fun k : Fin (n + 1) => S.matrix r k * bitValue (ZMod 2)
      (permute j (Fin.cons (α := fun _ : Fin (n + 1) => Bool) bit x) k))
  simp only [permute, Equiv.swap_apply_self] at hs
  simp only [rowDot, permute]
  rw [← hs, Fin.sum_univ_succ]
  simp [hj, tailRow, dot]

theorem holds_forces_bit {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1))
    (hj : S.matrix r j = 1) (bit : Bool) (x : Word n)
    (h : S.Holds (permute j (Fin.cons bit x))) : bit = selectedBit S r j x := by
  apply bitValue_injective
  rw [selectedBit, bitValue_residueBit]
  have hr := h r
  change rowDot (S.matrix r) (permute j (Fin.cons bit x)) = S.rhs r at hr
  rw [selected_row S r j hj] at hr
  exact eq_sub_iff_add_eq.mpr hr

noncomputable def eliminate {n : ℕ} (A : State (n + 1)) (r : Fin A.support.rows) (j : Fin (n + 1)) : State n where
  scale := A.scale
  support := A.support.pullback (solveMap A.support r j)
  phase := Reconstruction.pullback A.phase (solveMap A.support r j) (solveMap_affine A.support r j)

theorem eliminate_value {n : ℕ} (A : State (n + 1)) (r : Fin A.support.rows) (j : Fin (n + 1)) (x : Word n) :
    (eliminate A r j).value x = A.value (solveMap A.support r j x) := by
  simp [State.value, affineFormula, eliminate, AffineSystem.pullback_holds,
    solveMap_affine, Reconstruction.pullback_eval]

theorem partition_eliminate {n : ℕ} (A : State (n + 1)) (r : Fin A.support.rows) (j : Fin (n + 1))
    (hj : A.support.matrix r j = 1) : A.partition = (eliminate A r j).partition := by
  rw [State.partition, sum_permuted_split _ j, State.partition]
  apply Finset.sum_congr rfl
  intro x _
  rw [eliminate_value]
  have wrong (bit : Bool) (hb : bit ≠ selectedBit A.support r j x) :
      A.value (permute j (Fin.cons bit x)) = 0 := by
    have hn : ¬ A.support.Holds (permute j (Fin.cons bit x)) :=
      fun h => hb (holds_forces_bit A.support r j hj bit x h)
    simp [State.value, affineFormula, hn]
  cases hb : selectedBit A.support r j x with
  | false => simp [solveMap, hb, wrong true (by simp [hb])]
  | true => simp [solveMap, hb, wrong false (by simp [hb])]

theorem partition_badRow {n : ℕ} (A : State n) (h : badRow A.support = true) : A.partition = 0 := by
  simp [State.partition, State.value, affineFormula, badRow_no_solution A.support h]

end Holant.LocalDrafts.Tractability.AffineMachine.Constraint
