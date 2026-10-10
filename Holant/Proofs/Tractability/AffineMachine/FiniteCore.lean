import Holant.Proofs.Tractability.AffineMachine.ScalarCode


namespace Holant.LocalDrafts.Tractability.AffineMachine.FiniteCore

open Holant.Tractable AffinePhase TwoTranslate ProductMachine
open scoped BigOperators

def zeroWord (n : ℕ) : Word n := fun _ => false
def singleton {n : ℕ} (j : Fin n) : Word n := fun k => decide (k = j)
def xorWord {n : ℕ} (x y : Word n) : Word n := fun j => Bool.xor (x j) (y j)

def bit2 (b : Bool) : ZMod 2 := if b then 1 else 0
def bit4 (b : Bool) : ZMod 4 := if b then 1 else 0

def dot {n : ℕ} (a : Fin n → ZMod 2) (x : Word n) : ZMod 2 :=
  (List.ofFn (fun j => a j * bit2 (x j))).sum

@[simp] theorem dot_eq {n : ℕ} (a : Fin n → ZMod 2) (x : Word n) : dot a x = TwoTranslate.dot a x := by
  simp [dot, TwoTranslate.dot, bit2, bitValue, List.sum_ofFn]

def phase {n : ℕ} (Q : QuadraticPhase n) (x : Word n) : ZMod 4 :=
  Q.constant + (List.ofFn (fun j => Q.linear j * bit4 (x j))).sum +
    (List.ofFn (fun j => (List.ofFn (fun k =>
      if j < k then Q.mixed j k * bit4 (x j) * bit4 (x k) else 0)).sum)).sum

@[simp] theorem phase_eq {n : ℕ} (Q : QuadraticPhase n) (x : Word n) : phase Q x = Q.eval x := by
  simp [phase, QuadraticPhase.eval, bit4, bitValue, List.sum_ofFn]

/-- Eager vector tables ensure sample results are stored, not recursively
recomputed through nested substitution closures. The proof argument is erased. -/
def reconstruct {n : ℕ} (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) : QuadraticPhase n :=
  let c := q (zeroWord n)
  let l := List.Vector.ofFn (fun j => q (singleton j))
  let m := List.Vector.ofFn (fun j => List.Vector.ofFn (fun k => q (xorWord (singleton j) (singleton k))))
  { constant := c
    linear := fun j => l.get j - c
    mixed := fun j k => (m.get j).get k - l.get j - l.get k + c
    even_mixed := fun j k _ => by
      dsimp only [c, l, m]
      simp only [List.Vector.get_ofFn]
      exact Reconstruction.mixed_even q hq j k }

theorem reconstruct_eq {n : ℕ} (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) :
    reconstruct q hq = Reconstruction.coefficients q hq := by
  simp only [reconstruct, List.Vector.get_ofFn]
  rfl

def solve {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1)) (x : Word n) :
    Word (n + 1) :=
  let a := S.rhs r - dot (fun k => S.matrix r (Equiv.swap 0 j k.succ)) x
  let w := List.Vector.ofFn (Fin.cons (decide (a = 1)) x)
  fun k => w.get (Equiv.swap 0 j k)

@[simp] theorem solve_eq {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows)
    (j : Fin (n + 1)) (x : Word n) : solve S r j x = Constraint.solveMap S r j x := by
  funext k
  simp [solve, Constraint.solveMap, Constraint.selectedBit, Constraint.tailRow, permute, residueBit]
  rfl

def supportStep {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1)) : AffineSystem n where
  rows := S.rows
  matrix t k := dot (S.matrix t) (solve S r j (singleton k)) - dot (S.matrix t) (solve S r j (zeroWord n))
  rhs t := S.rhs t - dot (S.matrix t) (solve S r j (zeroWord n))

theorem supportStep_eq {n : ℕ} (S : AffineSystem (n + 1)) (r : Fin S.rows) (j : Fin (n + 1)) :
    supportStep S r j = S.pullback (Constraint.solveMap S r j) := by
  simp only [supportStep, dot_eq, solve_eq]
  rfl

def phaseStep {n : ℕ} (S : AffineSystem (n + 1)) (Q : QuadraticPhase (n + 1))
    (r : Fin S.rows) (j : Fin (n + 1)) : QuadraticPhase n :=
  reconstruct (fun x => phase Q (solve S r j x)) (by
    simpa only [phase_eq, solve_eq] using
      Reconstruction.precompose_third Q (Constraint.solveMap S r j) (Constraint.solveMap_affine S r j))

theorem phaseStep_eq {n : ℕ} (S : AffineSystem (n + 1)) (Q : QuadraticPhase (n + 1))
    (r : Fin S.rows) (j : Fin (n + 1)) :
    phaseStep S Q r j = Reconstruction.pullback Q (Constraint.solveMap S r j) (Constraint.solveMap_affine S r j) := by
  simp only [phaseStep, reconstruct_eq, phase_eq, solve_eq, Reconstruction.pullback]

def neighbors {n : ℕ} (Q : QuadraticPhase (n + 1)) : Fin n → ZMod 2 :=
  fun j => if Q.mixed 0 j.succ = 0 then 0 else 1

def tail {n : ℕ} (Q : QuadraticPhase (n + 1)) : QuadraticPhase n where
  constant := Q.constant
  linear j := Q.linear j.succ
  mixed j k := Q.mixed j.succ k.succ
  even_mixed j k h := Q.even_mixed j.succ k.succ (by simpa using h)

def parity {n : ℕ} (Q : QuadraticPhase n) (a : Fin n → ZMod 2) (t : ZMod 4) : QuadraticPhase n :=
  reconstruct (fun x => phase Q x + t * (if dot a x = 0 then 0 else 1)) (by
    intro z u v w
    simp only [phase_eq, dot_eq]
    change thirdDifference (fun x => Q.eval x + t * bitLift (TwoTranslate.dot a x)) z u v w = 0
    rw [thirdDifference_add, quadratic_thirdDifference, thirdDifference_mul_const, bitLift_dot_thirdDifference]
    simp)

theorem parity_eq {n : ℕ} (Q : QuadraticPhase n) (a : Fin n → ZMod 2) (t : ZMod 4) :
    parity Q a t = Reconstruction.addParity Q a t := by
  simp [parity, reconstruct_eq, Reconstruction.addParity, bitLift]

def freeSupport {n : ℕ} (Q : QuadraticPhase (n + 1)) : AffineSystem n :=
  if Q.linear 0 = 0 then ⟨1, fun _ => neighbors Q, fun _ => 0⟩ else
    if Q.linear 0 = 1 then ⟨0, Fin.elim0, Fin.elim0⟩ else
      if Q.linear 0 = 2 then ⟨1, fun _ => neighbors Q, fun _ => 1⟩ else ⟨0, Fin.elim0, Fin.elim0⟩

def freePhase {n : ℕ} (Q : QuadraticPhase (n + 1)) : QuadraticPhase n :=
  if Q.linear 0 = 0 then tail Q else
    if Q.linear 0 = 1 then parity (tail Q) (neighbors Q) (-1) else
      if Q.linear 0 = 2 then tail Q else parity (tail Q) (neighbors Q) 1

@[simp] theorem freeSupport_eq {n : ℕ} (Q : QuadraticPhase (n + 1)) : freeSupport Q = FreePhase.nextSupport Q := rfl

@[simp] theorem freePhase_eq {n : ℕ} (Q : QuadraticPhase (n + 1)) : freePhase Q = FreePhase.nextPhase Q := by
  simp only [freePhase, FreePhase.nextPhase, parity_eq]
  rfl

def pivotStep {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows) (j : Fin (n + 1)) : Dense.Table n :=
  Dense.snapshot (supportStep T.support r j) (phaseStep T.support T.phase r j)

def freeStep {n : ℕ} (T : Dense.Table (n + 1)) : Dense.Table n :=
  Dense.snapshot (freeSupport T.phase) (freePhase T.phase)

@[simp] theorem pivotStep_eq {n : ℕ} (T : Dense.Table (n + 1)) (r : Fin T.rows) (j : Fin (n + 1)) :
    pivotStep T r j = Dense.pivotStep T r j := by
  have hs := supportStep_eq T.support r j
  have hp := phaseStep_eq T.support T.phase r j
  unfold pivotStep Dense.pivotStep
  exact congrArg₂ Dense.snapshot hs (hp.trans (SampleTable.pullback_eq _ _ _).symm)

@[simp] theorem freeStep_eq {n : ℕ} (T : Dense.Table (n + 1)) : freeStep T = Dense.freeStep T := by
  simp [freeStep, Dense.freeStep]

/-- No runtime constants from an infinite coefficient field appear here. -/
def compile {A : Type} : {n : ℕ} → Dense.Table n → Expr (ScalarCode.Atom A) → Expr (ScalarCode.Atom A)
  | 0, T, e => if Constraint.badRow T.support then .zero else .mul e (.literal (.inr (.inl T.constant)))
  | n + 1, T, e => if Constraint.badRow T.support then .zero else
      match Constraint.pivot T.support with
      | some (r, j) => compile (pivotStep T r j) e
      | none => compile (freeStep T) (.mul e (.literal (.inr (.inr (T.phase.linear 0)))))

theorem compile_eq {A : Type} : ∀ {n : ℕ} (T : Dense.Table n) (e : Expr (ScalarCode.Atom A)),
    compile T e = ScalarCode.compile T e := by
  intro n
  induction n with
  | zero => intro T e; rfl
  | succ n ih =>
    intro T e
    simp only [compile, ScalarCode.compile]
    split
    · rfl
    · cases hp : Constraint.pivot T.support with
      | none => simp only [hp, ih, freeStep_eq]
      | some p =>
        rcases p with ⟨r,j⟩
        simp only [hp, ih]
        exact congrArg (fun U => ScalarCode.compile U e) (pivotStep_eq T r j)

theorem compile_correct {A : Type} (c : A → AlgebraicComplex) {n : ℕ}
    (T : Dense.Table n) (e : Expr (ScalarCode.Atom A)) :
    (compile T e).eval (ScalarCode.coefficient c) = (T.state (e.eval (ScalarCode.coefficient c))).partition := by
  rw [compile_eq]
  exact ScalarCode.compile_correct c T e

theorem compile_size {A : Type} {n : ℕ} (T : Dense.Table n) (e : Expr (ScalarCode.Atom A)) :
    (compile T e).size ≤ e.size + 2 * n + 2 := by rw [compile_eq]; exact ScalarCode.compile_size T e

/-- The number of selected runtime transitions, following exactly compile's
branch tests; inconsistent input may terminate before dimension reaches zero. -/
def transitions : {n : ℕ} → Dense.Table n → ℕ
  | 0, _ => 0
  | n + 1, T => if Constraint.badRow T.support then 0 else
      match Constraint.pivot T.support with
      | some (r, j) => 1 + transitions (pivotStep T r j)
      | none => 1 + transitions (freeStep T)

theorem transitions_le : ∀ {n : ℕ} (T : Dense.Table n), transitions T ≤ n := by
  intro n
  induction n with
  | zero => intro T; simp [transitions]
  | succ n ih =>
    intro T
    unfold transitions
    split
    · omega
    · split <;> simpa only [Nat.add_comm] using Nat.add_le_add_left (ih _) 1

end Holant.LocalDrafts.Tractability.AffineMachine.FiniteCore
