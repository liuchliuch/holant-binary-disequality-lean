import Holant.Proofs.Algorithms.LocalAffine.SupportSystem
import Holant.Proofs.Tractability.AffineMachine.FiniteCore


namespace Holant.LocalDrafts.MainChain.LocalAffineSupportSolver
open Holant.Tractable AffinePhase TwoTranslate
open Holant.LocalDrafts.Tractability.AffineMachine

/-- Materialize every coefficient before recursing; substitution closures do
not grow through the recursion. -/
def snapshot {n : ℕ} (S : AffineSystem n) : AffineSystem n :=
  let matrix := List.Vector.ofFn (fun r => List.Vector.ofFn (S.matrix r))
  let rhs := List.Vector.ofFn S.rhs
  { rows := S.rows, matrix := fun r j => (matrix.get r).get j, rhs := rhs.get }

theorem snapshot_eq {n : ℕ} (S : AffineSystem n) : snapshot S = S := by
  cases S
  simp [snapshot]
  funext r
  simp

def descend {n : ℕ} (S : AffineSystem (n+1)) (r : Fin S.rows) (j : Fin (n+1)) :
    AffineSystem n := snapshot (FiniteCore.supportStep S r j)

theorem descend_eq {n : ℕ} (S : AffineSystem (n+1)) (r : Fin S.rows) (j : Fin (n+1)) :
    descend S r j = S.pullback (Constraint.solveMap S r j) := by
  rw [descend, snapshot_eq, FiniteCore.supportStep_eq]

def solve : {n : ℕ} → AffineSystem n → Option (Word n)
  | 0, S => if Constraint.badRow S then none else some Fin.elim0
  | n+1, S =>
    if Constraint.badRow S then none else
      match Constraint.pivot S with
      | none => some (FiniteCore.zeroWord (n+1))
      | some (r,j) => (solve (descend S r j)).map (FiniteCore.solve S r j)

theorem nullary_holds (S : AffineSystem 0) (hb : Constraint.badRow S = false) :
    S.Holds Fin.elim0 := by
  apply Constraint.no_pivot_holds S _ hb
  have hn : (List.finRange S.rows).flatMap (fun _ => ([] : List (Fin S.rows × Fin 0))) = [] :=
    List.flatMap_eq_nil_iff.mpr (by simp)
  simpa [Constraint.pivot, Constraint.positions, hn] using
    (show Constraint.first (fun p : Fin S.rows × Fin 0 => !decide (S.matrix p.1 p.2 = 0)) [] = none from rfl)

theorem solve_sound : ∀ {n : ℕ} (S : AffineSystem n) (x : Word n),
    solve S = some x → S.Holds x := by
  intro n
  induction n with
  | zero =>
    intro S x hx
    cases hb : Constraint.badRow S with
    | true => simp [solve,hb] at hx
    | false =>
      have he : Fin.elim0 = x := by simpa [solve,hb] using hx
      rw [←he]
      exact nullary_holds S hb
  | succ n ih =>
    intro S x hx
    cases hb : Constraint.badRow S with
    | true => simp [solve,hb] at hx
    | false =>
      cases hp : Constraint.pivot S with
      | none => exact Constraint.no_pivot_holds S hp hb x
      | some p =>
        rcases p with ⟨r,j⟩
        cases hy : solve (descend S r j) with
        | none => simp [solve,hb,hp,hy] at hx
        | some y =>
          have hxy : FiniteCore.solve S r j y = x := by
            simpa [solve,hb,hp,hy] using hx
          have hs := ih (descend S r j) y hy
          rw [descend_eq, AffineSystem.pullback_holds _ _
            (Constraint.solveMap_affine S r j)] at hs
          rwa [←FiniteCore.solve_eq, hxy] at hs

/-- The solved coordinate is forced by the selected actual row. Therefore
projection of any solution is a solution of the smaller system. -/
theorem descend_has_solution {n : ℕ} (S : AffineSystem (n+1))
    (r : Fin S.rows) (j : Fin (n+1)) (hj : S.matrix r j = 1)
    (z : Word (n+1)) (hz : S.Holds z) : ∃ y, (descend S r j).Holds y := by
  let w := permute j z
  let y := Fin.tail w
  have hperm : permute j (Fin.cons (w 0) y) = z := by
    rw [show Fin.cons (w 0) y = w from Fin.cons_self_tail w]
    funext i
    simp [w,permute]
  have hb := Constraint.holds_forces_bit S r j hj (w 0) y (by simpa only [hperm] using hz)
  have hs : Constraint.solveMap S r j y = z := by
    unfold Constraint.solveMap
    rw [←hb]
    exact hperm
  refine ⟨y, ?_⟩
  rw [descend_eq, AffineSystem.pullback_holds _ _ (Constraint.solveMap_affine S r j), hs]
  exact hz

theorem solve_complete : ∀ {n : ℕ} (S : AffineSystem n),
    (∃ x, S.Holds x) → ∃ y, solve S = some y := by
  intro n
  induction n with
  | zero =>
    intro S hs
    obtain ⟨x,hx⟩ := hs
    cases hb : Constraint.badRow S with
    | true => exact (Constraint.badRow_no_solution S hb x hx).elim
    | false => exact ⟨Fin.elim0, by simp [solve,hb]⟩
  | succ n ih =>
    intro S hs
    obtain ⟨x,hx⟩ := hs
    cases hb : Constraint.badRow S with
    | true => exact (Constraint.badRow_no_solution S hb x hx).elim
    | false =>
      cases hp : Constraint.pivot S with
      | none => exact ⟨FiniteCore.zeroWord (n+1), by simp [solve,hb,hp]⟩
      | some p =>
        rcases p with ⟨r,j⟩
        obtain ⟨y,hy⟩ := ih (descend S r j)
          (descend_has_solution S r j (Constraint.pivot_some S r j hp) x hx)
        exact ⟨FiniteCore.solve S r j y, by simp [solve,hb,hp,hy]⟩

theorem solve_none_iff {n : ℕ} (S : AffineSystem n) :
    solve S = none ↔ ¬ ∃ x, S.Holds x := by
  constructor
  · intro hn hs
    obtain ⟨y,hy⟩ := solve_complete S hs
    simp [hn] at hy
  · intro hn
    cases h : solve S with
    | none => rfl
    | some x => exact (hn ⟨x,solve_sound S x h⟩).elim

def rounds : {n : ℕ} → AffineSystem n → ℕ
  | 0, _ => 0
  | n+1, S => if Constraint.badRow S then 0 else
      match Constraint.pivot S with
      | none => 0
      | some (r,j) => 1 + rounds (descend S r j)

theorem rounds_le : ∀ {n : ℕ} (S : AffineSystem n), rounds S ≤ n := by
  intro n
  induction n with
  | zero => intro S; simp [rounds]
  | succ n ih =>
    intro S
    cases hb : Constraint.badRow S with
    | true => simp [rounds, hb]
    | false =>
      cases hp : Constraint.pivot S with
      | none => simp [rounds, hb, hp]
      | some p =>
        rcases p with ⟨r, j⟩
        have h := ih (descend S r j)
        simp only [rounds, hb, Bool.false_eq_true, ↓reduceIte, hp]
        omega

theorem descend_rows {n : ℕ} (S : AffineSystem (n+1)) (r : Fin S.rows) (j : Fin (n+1)) :
    (descend S r j).rows = S.rows := rfl

end Holant.LocalDrafts.MainChain.LocalAffineSupportSolver
