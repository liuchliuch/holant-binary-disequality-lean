import Holant.Proofs.Tractability.ProductMachine.Compilation


namespace Holant.LocalDrafts.Tractability.ProductMachine.Semantics

open ProductElimination (LabelledFactor)
open Templates (Record)

theorem selected_cons (r : Record) (rs : List Record) :
    PivotScan.selected (r :: rs) =
      if PivotScan.eligible r then PivotScan.candidate r else PivotScan.selected rs := by
  cases h : PivotScan.eligible r <;> simp [PivotScan.selected, PivotScan.candidates, h]

theorem selected_records {n : ℕ} (fs : List (LabelledFactor ℕ (n + 1))) :
    PivotScan.selected (fs.map Isolated.record) =
      match Symbolic.pivot fs with
      | none => (0, false)
      | some (j, p) => (j.val + 1, p) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [List.map_cons, selected_cons]
    cases f with
    | scalar a => simpa [Isolated.record, PivotScan.eligible, Symbolic.pivot,
        LabelledFactor.realize, ProductElimination.pivot, ProductElimination.Factor.pivot] using ih
    | unary j a => simpa [Isolated.record, PivotScan.eligible, Symbolic.pivot,
        LabelledFactor.realize, ProductElimination.pivot, ProductElimination.Factor.pivot] using ih
    | link i j p =>
      refine Fin.cases ?_ (fun i => ?_) i
      all_goals refine Fin.cases ?_ (fun j => ?_) j
      all_goals cases p <;>
        simp_all [Isolated.record, PivotScan.eligible, PivotScan.candidate, Symbolic.pivot,
          LabelledFactor.realize, ProductElimination.pivot, ProductElimination.Factor.pivot,
          Fin.succ_ne_zero]

theorem rewrite_record {n : ℕ} (f : LabelledFactor ℕ (n + 1)) (j : Fin n) (p : Bool) :
    Rewrite.record (j.val + 1, p) (Isolated.record f) =
      Isolated.record (Symbolic.substitute (ProductElimination.redirect j p) f) := by
  cases f with
  | scalar a => rfl
  | unary i a =>
    refine Fin.cases ?_ (fun i => ?_) i
    all_goals cases p <;> simp [Isolated.record, Rewrite.record, Rewrite.address,
      Rewrite.flipAt, Symbolic.substitute, ProductElimination.redirect, Fin.succ_ne_zero]
  | link i k t =>
    refine Fin.cases ?_ (fun i => ?_) i
    all_goals refine Fin.cases ?_ (fun k => ?_) k
    all_goals cases p <;> cases t <;> simp [Isolated.record, Rewrite.record, Rewrite.address,
      Rewrite.flipAt, Symbolic.substitute, ProductElimination.redirect, Fin.succ_ne_zero]

def state {n : ℕ} (fs : List (LabelledFactor ℕ n)) (acc : Expr ℕ) : Round.State :=
  (n, fs.map Isolated.record, acc)

theorem step_state {n : ℕ} (fs : List (LabelledFactor ℕ (n + 1))) (acc : Expr ℕ) :
    Round.step (state fs acc) =
      match Symbolic.pivot fs with
      | none => state (Symbolic.tail fs) (.mul acc (.add (Symbolic.head fs false) (Symbolic.head fs true)))
      | some (j, p) => state (fs.map (Symbolic.substitute (ProductElimination.redirect j p))) acc := by
  cases h : Symbolic.pivot fs with
  | none => simp [state, Round.step, selected_records, h, Isolated.multiplier,
      Isolated.head_records, Isolated.tail_records]
  | some jp =>
    rcases jp with ⟨j, p⟩
    simp [state, Round.step, selected_records, h, List.map_map, Function.comp_def, rewrite_record]

/-- Typed source counterpart of the actual accumulator machine. -/
def compileAcc {A : Type} : {n : ℕ} → List (LabelledFactor A n) → Expr A → Expr A
  | 0, fs, acc => .mul acc (Expr.product (fs.map (fun f => Symbolic.atom f Fin.elim0)))
  | n + 1, fs, acc => match Symbolic.pivot fs with
    | none => compileAcc (Symbolic.tail fs) (.mul acc (.add (Symbolic.head fs false) (Symbolic.head fs true)))
    | some (j, p) => compileAcc (fs.map (Symbolic.substitute (ProductElimination.redirect j p))) acc

theorem scalar_record (f : LabelledFactor ℕ 0) :
    Compilation.scalar (Isolated.record f) = Symbolic.atom f Fin.elim0 := by
  cases f with
  | scalar a => rfl
  | unary j a => exact Fin.elim0 j
  | link i j p => exact Fin.elim0 i

theorem finish_iterate {n : ℕ} (fs : List (LabelledFactor ℕ n)) (acc : Expr ℕ) :
    Compilation.finish ((Round.step^[n]) (state fs acc)) = compileAcc fs acc := by
  induction n generalizing acc with
  | zero => simp [Compilation.finish, state, compileAcc, List.map_map, Function.comp_def, scalar_record]
  | succ n ih =>
    rw [Function.iterate_succ_apply, step_state]
    cases hp : Symbolic.pivot fs with
    | none => simpa [compileAcc, hp] using (ih (Symbolic.tail fs)
        (.mul acc (.add (Symbolic.head fs false) (Symbolic.head fs true))))
    | some jp =>
      rcases jp with ⟨j, p⟩
      simpa [compileAcc, hp] using ih (fs.map (Symbolic.substitute (ProductElimination.redirect j p))) acc

theorem stateExpression_eq {n : ℕ} (fs : List (LabelledFactor ℕ n)) (acc : Expr ℕ) :
    Compilation.stateExpression (state fs acc) = compileAcc fs acc :=
  finish_iterate fs acc

theorem compileAcc_eval {A K : Type} [CommSemiring K] (coeff : A → K)
    {n : ℕ} (fs : List (LabelledFactor A n)) (acc : Expr A) :
    (compileAcc fs acc).eval coeff =
      acc.eval coeff * ProductElimination.evaluate (fs.map (LabelledFactor.realize coeff)) := by
  induction n generalizing acc with
  | zero => simp [compileAcc, Expr.eval, Expr.eval_product, Symbolic.atom_eval,
      ProductElimination.evaluate, ProductElimination.weight, List.map_map, Function.comp_def]
  | succ n ih =>
    cases hp : Symbolic.pivot fs with
    | none => simp [compileAcc, hp, ih, Expr.eval, ProductElimination.evaluate,
        Symbolic.pivot_realize, Symbolic.head_eval, Symbolic.tail_realize, mul_assoc]
    | some jp =>
      rcases jp with ⟨j, p⟩
      simp [compileAcc, hp, ih, ProductElimination.evaluate, Symbolic.pivot_realize,
        List.map_map, Function.comp_def, Symbolic.substitute_realize]

theorem compileAcc_size {A : Type} {n : ℕ} (fs : List (LabelledFactor A n)) (acc : Expr A) :
    (compileAcc fs acc).size ≤ acc.size + n * (4 * fs.length + 4) + 2 * fs.length + 2 := by
  induction n generalizing acc with
  | zero =>
    have h := Expr.size_product_le (fs.map (fun f => Symbolic.atom f Fin.elim0)) (by
      intro e he
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp he
      exact le_of_eq (Symbolic.atom_size f Fin.elim0))
    simp only [compileAcc, Expr.size, List.length_map] at *
    omega
  | succ n ih =>
    cases hp : Symbolic.pivot fs with
    | none =>
      have h := ih (Symbolic.tail fs) (.mul acc (.add (Symbolic.head fs false) (Symbolic.head fs true)))
      have hf := Symbolic.head_size fs false
      have ht := Symbolic.head_size fs true
      have hl := Symbolic.tail_length fs
      simp only [compileAcc, hp, Expr.size] at *
      nlinarith
    | some jp =>
      rcases jp with ⟨j, p⟩
      have h := ih (fs.map (Symbolic.substitute (ProductElimination.redirect j p))) acc
      simp only [compileAcc, hp, List.length_map] at *
      nlinarith

/-- Semantic correctness of the actual output syntax, without a free algorithm
correctness assumption. The statement is for typed Product factors. -/
theorem encoded_algorithm_value {K : Type} [CommSemiring K] (coeff : ℕ → K)
    {n : ℕ} (fs : List (LabelledFactor ℕ n)) :
    (Compilation.stateExpression (state fs .one)).eval coeff =
      ProductElimination.partition (fs.map (LabelledFactor.realize coeff)) := by
  rw [stateExpression_eq, compileAcc_eval, ProductElimination.evaluate_eq_partition]
  simp [Expr.eval]

end Holant.LocalDrafts.Tractability.ProductMachine.Semantics
