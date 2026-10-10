import Holant.OneHot.StackProgram.Core

/-!
# Linear, continuation-free compilation of the actual tree evaluators

Each child and suffix is compiled once. The instruction list depends only on the
labelled input tree, not on its interpretation or any intermediate field value.
The theorems preserve arbitrary stack suffixes and identify the entire executed
arithmetic trace with the previously bounded `Arithmetic` trace.
-/

namespace Holant.OneHot.StackProgram

variable {A K : Type*}

mutual
/-- Interpret input coefficient labels, without changing the ordered tree. -/
def interpretTree (coeff : A → K) : Tree A → Tree K
  | .node a b ts => .node (coeff a) (coeff b) (interpretForest coeff ts)
def interpretForest (coeff : A → K) : Forest A → Forest K
  | .nil => .nil
  | .cons p t ts => .cons (coeff p) (interpretTree coeff t) (interpretForest coeff ts)
end

/-- Root block: `(empty, one)` becomes `(free, occupied)`; the arithmetic order
is exactly that of `Tree.program`. -/
def nodeCode (a b : A) : Code A :=
  [.copy 1, .copy 1, .literal a, .mul, .add,
   .copy 1, .literal b, .mul, .swap, .erase 2, .erase 2]

/-- Child-fold block, with each of the four child/suffix values shared. -/
def consCode (p : A) : Code A :=
  [.copy 0, .copy 4, .mul,
   .copy 3, .literal p, .mul,
   .copy 2, .swap, .mul,
   .copy 3, .copy 6, .mul,
   .swap, .add, .swap,
   .erase 2, .erase 2, .erase 2, .erase 2]

/-- The actual closed root has no unused parent-port coefficient. -/
def rootCode (a : A) : Code A := [.literal a, .mul, .add]

mutual
/-- Finite serial instruction list for a tree. -/
def compileTree : Tree A → Code A
  | .node a b ts => compileForest ts ++ nodeCode a b
/-- Finite child fold, with no recursive duplication of child computations. -/
def compileForest : Forest A → Code A
  | .nil => [.zero, .one]
  | .cons p t ts => compileTree t ++ compileForest ts ++ consCode p
end

def compileClosed (a : A) (ts : Forest A) : Code A := compileForest ts ++ rootCode a

variable [CommSemiring K]

@[simp] theorem run_nodeCode (coeff : A → K) (a b : A) (x y : K) (s : List K) :
    run coeff (nodeCode a b) (x :: y :: s) =
      some ((coeff a * x + y) :: (coeff b * x) :: s,
        [coeff a, x, coeff a * x, coeff a * x, y, coeff a * x + y,
         coeff b, x, coeff b * x]) := by
  simp [nodeCode, run, step, eraseAt]

@[simp] theorem run_consCode (coeff : A → K) (p : A) (c₀ c₁ x y : K) (s : List K) :
    run coeff (consCode p) (x :: y :: c₀ :: c₁ :: s) =
      some ((c₁ * x) :: (coeff p * c₀ * x + c₁ * y) :: s,
        [c₁, x, c₁ * x, coeff p, c₀, coeff p * c₀,
         coeff p * c₀, x, coeff p * c₀ * x,
         c₁, y, c₁ * y, coeff p * c₀ * x, c₁ * y,
         coeff p * c₀ * x + c₁ * y]) := by
  simp [consCode, run, step, eraseAt]

@[simp] theorem run_rootCode (coeff : A → K) (a : A) (x y : K) (s : List K) :
    run coeff (rootCode a) (x :: y :: s) =
      some ((coeff a * x + y) :: s,
        [coeff a, x, coeff a * x, coeff a * x, y, coeff a * x + y]) := by
  simp [rootCode, run, step]

mutual
/-- Exact output stack and every actually executed arithmetic operand/result. -/
theorem run_compileTree (coeff : A → K) (t : Tree A) (s : List K) :
    run coeff (compileTree t) s =
      some ((interpretTree coeff t).eval.1 :: (interpretTree coeff t).eval.2 :: s,
        (interpretTree coeff t).program.values) := by
  cases t with
  | node a b ts =>
    simp only [compileTree, run_append, run_compileForest, interpretTree,
      Tree.program, bind, pure, Arithmetic.values_bind, Forest.program_run,
      Arithmetic.run_mulOp, Arithmetic.run_addOp, Arithmetic.values_mulOp,
      Arithmetic.values_addOp, Arithmetic.values_pure, List.append_nil]
    simp [run_nodeCode, Tree.eval]
theorem run_compileForest (coeff : A → K) (ts : Forest A) (s : List K) :
    run coeff (compileForest ts) s =
      some ((interpretForest coeff ts).eval.1 :: (interpretForest coeff ts).eval.2 :: s,
        (interpretForest coeff ts).program.values) := by
  cases ts with
  | nil => simp [compileForest, interpretForest, Forest.eval, Forest.program,
      pure, run, step]
  | cons p t ts =>
    simp only [compileForest, List.append_assoc, run_append, run_compileTree,
      run_compileForest, interpretForest, Forest.program, bind, pure,
      Arithmetic.values_bind, Tree.program_run, Forest.program_run,
      Arithmetic.run_mulOp, Arithmetic.run_addOp, Arithmetic.values_mulOp,
      Arithmetic.values_addOp, Arithmetic.values_pure, List.append_nil]
    simp [run_consCode, Forest.eval]
end

/-- Closed-root output and trace, including the singleton nullary root. -/
theorem run_compileClosed (coeff : A → K) (a : A) (ts : Forest A) (s : List K) :
    run coeff (compileClosed a ts) s =
      some (((interpretForest coeff ts).closedProgram (coeff a)).run.1 :: s,
        ((interpretForest coeff ts).closedProgram (coeff a)).values) := by
  simp only [compileClosed, run_append, run_compileForest,
    Forest.closedProgram, bind, Arithmetic.values_bind, Forest.program_run,
    Arithmetic.run_mulOp, Arithmetic.values_mulOp, Arithmetic.values_addOp]
  simp [run_rootCode, Forest.program_run]

/-- Independent endpoint-choice semantics of the compiled tree. -/
theorem compileTree_denote (coeff : A → K) (t : Tree A) (s : List K) :
    (run coeff (compileTree t) s).map Prod.fst =
      some ((interpretTree coeff t).denote false ::
        (interpretTree coeff t).denote true :: s) := by
  simp [run_compileTree, Tree.eval_correct]

/-- The actual closed network, with no virtual root port or supplied pin. -/
theorem compileClosed_denote (coeff : A → K) (a : A) (ts : Forest A) (s : List K) :
    (run coeff (compileClosed a ts) s).map Prod.fst =
      some (((interpretForest coeff ts).closedNetwork (coeff a)).denote Fin.elim0 :: s) := by
  simp [run_compileClosed, Forest.closedProgram_network_spec]

omit [CommSemiring K]

mutual
@[simp] theorem length_compileTree (t : Tree A) :
    (compileTree t).length = 13 * t.vertices + 19 * t.edges := by
  cases t with
  | node a b ts =>
    simp only [compileTree, List.length_append, length_compileForest,
      nodeCode, List.length_cons, List.length_nil, Tree.vertices, Tree.edges]
    omega
@[simp] theorem length_compileForest (ts : Forest A) :
    (compileForest ts).length = 13 * ts.vertices + 19 * ts.edges + 2 := by
  cases ts with
  | nil => rfl
  | cons p t ts =>
    simp only [compileForest, List.length_append, length_compileTree,
      length_compileForest, consCode, List.length_cons, List.length_nil,
      Forest.vertices, Forest.edges]
    omega
end

@[simp] theorem length_compileClosed (a : A) (ts : Forest A) :
    (compileClosed a ts).length = 13 * ts.vertices + 19 * ts.edges + 5 := by
  simp [compileClosed, rootCode]

end Holant.OneHot.StackProgram
