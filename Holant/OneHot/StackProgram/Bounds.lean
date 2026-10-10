import Holant.OneHot.StackProgram.Tree

/-!
# Transport of actual intermediate-value bounds to finite stack execution

The transfer uses equality of the full executed arithmetic traces, not merely
agreement of final answers. All literal labels belong to the fixed coefficient
interpretation. Code length and certificate degree are linear in the input tree.
-/

namespace Holant.OneHot.StackProgram

variable {A K : Type*}

mutual
@[simp] theorem interpretTree_vertices (coeff : A → K) (t : Tree A) :
    (interpretTree coeff t).vertices = t.vertices := by
  cases t with
  | node a b ts => simp [interpretTree, Tree.vertices, interpretForest_vertices]
@[simp] theorem interpretForest_vertices (coeff : A → K) (ts : Forest A) :
    (interpretForest coeff ts).vertices = ts.vertices := by
  cases ts with
  | nil => rfl
  | cons p t ts => simp [interpretForest, Forest.vertices,
      interpretTree_vertices, interpretForest_vertices]
end

mutual
@[simp] theorem interpretTree_edges (coeff : A → K) (t : Tree A) :
    (interpretTree coeff t).edges = t.edges := by
  cases t with
  | node a b ts => simp [interpretTree, Tree.edges, interpretForest_edges]
@[simp] theorem interpretForest_edges (coeff : A → K) (ts : Forest A) :
    (interpretForest coeff ts).edges = ts.edges := by
  cases ts with
  | nil => rfl
  | cons p t ts => simp [interpretForest, Forest.edges,
      interpretTree_edges, interpretForest_edges]
end

mutual
@[simp] theorem interpretTree_id (t : Tree A) : interpretTree id t = t := by
  cases t with
  | node a b ts => simp [interpretTree, interpretForest_id]
@[simp] theorem interpretForest_id (ts : Forest A) : interpretForest id ts = ts := by
  cases ts with
  | nil => rfl
  | cons p t ts => simp [interpretForest, interpretTree_id, interpretForest_id]
end

variable [CommSemiring K]

mutual
/-- Each label is a member of the fixed coefficient family by construction. -/
theorem interpretTree_all (coeff : A → K) (t : Tree A) :
    (interpretTree coeff t).All (ArithmeticSize.Bound coeff 1) := by
  cases t with
  | node a b ts =>
    exact ⟨ArithmeticSize.Bound.coefficient a, ArithmeticSize.Bound.coefficient b,
      interpretForest_all coeff ts⟩
theorem interpretForest_all (coeff : A → K) (ts : Forest A) :
    (interpretForest coeff ts).All (ArithmeticSize.Bound coeff 1) := by
  cases ts with
  | nil => trivial
  | cons p t ts =>
    exact ⟨ArithmeticSize.Bound.coefficient p, interpretTree_all coeff t,
      interpretForest_all coeff ts⟩
end

/-- Any proved executed-value property of the continuation evaluator transfers. -/
theorem safe_compileTree (coeff : A → K) (t : Tree A) (s : List K) (P : K → Prop)
    (h : Arithmetic.Safe P (interpretTree coeff t).program) :
    Safe coeff P (compileTree t) s :=
  ⟨_, _, run_compileTree coeff t s, h⟩

theorem safe_compileForest (coeff : A → K) (ts : Forest A) (s : List K) (P : K → Prop)
    (h : Arithmetic.Safe P (interpretForest coeff ts).program) :
    Safe coeff P (compileForest ts) s :=
  ⟨_, _, run_compileForest coeff ts s, h⟩

theorem safe_compileClosed (coeff : A → K) (a : A) (ts : Forest A)
    (s : List K) (P : K → Prop)
    (h : Arithmetic.Safe P ((interpretForest coeff ts).closedProgram (coeff a))) :
    Safe coeff P (compileClosed a ts) s :=
  ⟨_, _, run_compileClosed coeff a ts s, h⟩

/-- Actual stack arithmetic operands/results have a linear structural budget. -/
theorem compileTree_bound (coeff : A → K) (aone : A) (hone : coeff aone = 1)
    (t : Tree A) (s : List K) :
    Safe coeff (ArithmeticSize.Bound coeff (2 * (t.vertices + t.edges)))
      (compileTree t) s := by
  apply safe_compileTree
  have h := (ArithmeticSize.tree_program_bound aone hone
    (interpretTree coeff t) (interpretTree_all coeff t)).2.2
  simpa [ArithmeticSize.treeBudget] using h

theorem compileForest_bound (coeff : A → K) (aone : A) (hone : coeff aone = 1)
    (ts : Forest A) (s : List K) :
    Safe coeff (ArithmeticSize.Bound coeff (2 * (ts.vertices + ts.edges)))
      (compileForest ts) s := by
  apply safe_compileForest
  have h := (ArithmeticSize.forest_program_bound aone hone
    (interpretForest coeff ts) (interpretForest_all coeff ts)).2.2
  simpa [ArithmeticSize.forestBudget] using h

theorem compileClosed_bound (coeff : A → K) (aone : A) (hone : coeff aone = 1)
    (a : A) (ts : Forest A) (s : List K) :
    Safe coeff (ArithmeticSize.Bound coeff (2 * (ts.vertices + ts.edges) + 2))
      (compileClosed a ts) s := by
  apply safe_compileClosed
  have h := (ArithmeticSize.closed_program_bound aone hone
    (interpretForest coeff ts) (coeff a) (interpretForest_all coeff ts)
    (ArithmeticSize.Bound.coefficient a)).2
  simpa [ArithmeticSize.forestBudget] using h

/-- The literal coefficient tree is compiled directly by choosing `id`. -/
theorem run_compileTree_literal (t : Tree K) (s : List K) :
    run id (compileTree t) s = some (t.eval.1 :: t.eval.2 :: s, t.program.values) := by
  simpa using run_compileTree id t s

/-- Exact opcode length expressed in the actual closed-network graph sizes. -/
theorem length_compileClosed_network (coeff : A → K) (a : A) (ts : Forest A) :
    (compileClosed a ts).length =
      13 * ((interpretForest coeff ts).closedNetwork (coeff a)).shape.vertices +
      19 * ((interpretForest coeff ts).closedNetwork (coeff a)).shape.edges - 8 := by
  simp only [length_compileClosed, Forest.closedNetwork_vertices,
    Forest.closedNetwork_edges, interpretForest_vertices, interpretForest_edges]
  omega

/-- The existing fixed-field binary-size theorem now controls every actual
operand and result executed by the finite stack program. -/
theorem compileClosed_encoded_bound {L : Type*} [Field L] [Algebra ℚ L]
    {n : ℕ} (F : Holant.Algebraic.FixedField L n) [Fintype A]
    (coeff : A → Fin n → ℚ) (aone : A) (hone : F.decode (coeff aone) = 1)
    (a : A) (ts : Forest A) (s : List L) :
    Safe (fun i => F.decode (coeff i))
      (fun x => (F.encoding.encode x).length ≤
        ArithmeticSize.bitBound F coeff (2 * (ts.vertices + ts.edges) + 2))
      (compileClosed a ts) s := by
  rcases compileClosed_bound (fun i => F.decode (coeff i)) aone hone a ts s with
    ⟨s', trace, hr, hb⟩
  refine ⟨s', trace, hr, ?_⟩
  intro x hx
  exact (hb x hx).encoded_length_le F coeff

end Holant.OneHot.StackProgram
