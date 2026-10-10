import Holant.Proofs.Tractability.AffineMachine.Elimination
import Holant.Proofs.Tractability.AffineMachine.SampleTable
import Mathlib.Data.Vector.Basic


namespace Holant.LocalDrafts.Tractability.AffineMachine.Dense

open Holant.Tractable AffinePhase TwoTranslate

abbrev Vec := List.Vector

structure Table (n : ℕ) where
  rows : ℕ
  matrix : Vec (Vec (ZMod 2) n) rows
  rhs : Vec (ZMod 2) rows
  constant : ZMod 4
  linear : Vec (ZMod 4) n
  mixed : Vec (Vec (ZMod 4) n) n
  even_mixed : ∀ j k, j < k → (mixed.get j).get k = 0 ∨ (mixed.get j).get k = 2

def Table.support {n : ℕ} (T : Table n) : AffineSystem n :=
  ⟨T.rows, fun r j => (T.matrix.get r).get j, T.rhs.get⟩

def Table.phase {n : ℕ} (T : Table n) : QuadraticPhase n :=
  ⟨T.constant, T.linear.get, fun j k => (T.mixed.get j).get k, T.even_mixed⟩

def snapshot {n : ℕ} (S : AffineSystem n) (Q : QuadraticPhase n) : Table n where
  rows := S.rows
  matrix := List.Vector.ofFn (fun r => List.Vector.ofFn (S.matrix r))
  rhs := List.Vector.ofFn S.rhs
  constant := Q.constant
  linear := List.Vector.ofFn Q.linear
  mixed := List.Vector.ofFn (fun j => List.Vector.ofFn (Q.mixed j))
  even_mixed j k h := by simpa using Q.even_mixed j k h

@[simp] theorem support_snapshot {n : ℕ} (S : AffineSystem n) (Q : QuadraticPhase n) :
    (snapshot S Q).support = S := by
  cases S
  simp [snapshot, Table.support,funext_iff]

@[simp] theorem phase_snapshot {n : ℕ} (S : AffineSystem n) (Q : QuadraticPhase n) :
    (snapshot S Q).phase = Q := by
  cases Q
  simp [snapshot, Table.phase,funext_iff]

def Table.state {n : ℕ} (T : Table n) (scale : AlgebraicComplex) : State n :=
  ⟨scale, T.support, T.phase⟩

noncomputable def pivotStep {n : ℕ} (T : Table (n + 1)) (r : Fin T.rows) (j : Fin (n + 1)) : Table n :=
  snapshot (T.support.pullback (Constraint.solveMap T.support r j))
    (SampleTable.pullback T.phase (Constraint.solveMap T.support r j)
      (Constraint.solveMap_affine T.support r j))

noncomputable def cachedNextPhase {n : ℕ} (Q : QuadraticPhase (n + 1)) : QuadraticPhase n :=
  if Q.linear 0 = 0 then FreePhase.tail Q else
    if Q.linear 0 = 1 then SampleTable.addParity (FreePhase.tail Q) (FreePhase.neighbors Q) (-1) else
      if Q.linear 0 = 2 then FreePhase.tail Q else SampleTable.addParity (FreePhase.tail Q) (FreePhase.neighbors Q) 1

@[simp] theorem cachedNextPhase_eq {n : ℕ} (Q : QuadraticPhase (n + 1)) :
    cachedNextPhase Q = FreePhase.nextPhase Q := by simp [cachedNextPhase, FreePhase.nextPhase]

noncomputable def freeStep {n : ℕ} (T : Table (n + 1)) : Table n :=
  snapshot (FreePhase.nextSupport T.phase) (cachedNextPhase T.phase)

@[simp] theorem pivotStep_state {n : ℕ} (T : Table (n + 1)) (scale : AlgebraicComplex)
    (r : Fin T.rows) (j : Fin (n + 1)) :
    (pivotStep T r j).state scale = Constraint.eliminate (T.state scale) r j := by
  simp [pivotStep, Table.state, Constraint.eliminate]

@[simp] theorem freeStep_state {n : ℕ} (T : Table (n + 1)) (scale : AlgebraicComplex) :
    (freeStep T).state (scale * FreePhase.multiplier (T.phase.linear 0)) =
      FreePhase.eliminate (T.state scale) := by
  simp [freeStep, Table.state, FreePhase.eliminate]

@[simp] theorem pivotStep_rows {n : ℕ} (T : Table (n + 1)) (r : Fin T.rows) (j : Fin (n + 1)) :
    (pivotStep T r j).rows = T.rows := rfl

theorem freeStep_rows {n : ℕ} (T : Table (n + 1)) : (freeStep T).rows ≤ 1 :=
  FreePhase.rows_le_one T.phase

/-- Exact number of binary/residue payload bits in the dense coefficients.
Dimensions, framing, indices, and the scalar expression are counted separately. -/
def payload (n m : ℕ) : ℕ := m * (n + 1) + 2 * (1 + n + n * n)

theorem payload_mono {n N m M : ℕ} (hn : n ≤ N) (hm : m ≤ M) :
    payload n m ≤ payload N M := by
  unfold payload
  gcongr

/-- A structural reachability relation for the actual selected branches. -/
inductive Reachable : {n m : ℕ} → Table n → Table m → Prop where
  | start {n} (T : Table n) : Reachable T T
  | pivot {N n} {T : Table N} {U : Table (n + 1)}
      (h : Reachable T U) (r : Fin U.rows) (j : Fin (n + 1))
      (hp : Constraint.pivot U.support = some (r, j)) : Reachable T (pivotStep U r j)
  | free {N n} {T : Table N} {U : Table (n + 1)}
      (h : Reachable T U) (hp : Constraint.pivot U.support = none) : Reachable T (freeStep U)

theorem reachable_bounds {N n : ℕ} {T : Table N} {U : Table n} (h : Reachable T U) :
    n ≤ N ∧ U.rows ≤ max T.rows 1 := by
  induction h with
  | start T => exact ⟨le_rfl, le_max_left _ _⟩
  | pivot h r j hp ih => exact ⟨by omega, by simpa using ih.2⟩
  | free h hp ih => exact ⟨by omega, (freeStep_rows _).trans (le_max_right _ _)⟩

theorem reachable_payload {N n : ℕ} {T : Table N} {U : Table n} (h : Reachable T U) :
    payload n U.rows ≤ payload N (max T.rows 1) :=
  payload_mono (reachable_bounds h).1 (reachable_bounds h).2

end Holant.LocalDrafts.Tractability.AffineMachine.Dense
