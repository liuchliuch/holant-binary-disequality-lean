import Holant.OneHot.Decomposition.TreeEvaluation
import Mathlib.Data.Finset.Sort

/-!
# Order-independent finite child folds

The executable builder uses sorted finite child lists. This algebraic interface
compares their values and sizes with the semantic finite-family construction,
without imposing the semantic construction's classical enumeration at runtime.
-/

namespace Holant.OneHot.Computable.Evaluation

variable {K : Type*}

/-- Two child-fold accumulators and the actual accumulated graph size. -/
@[ext] structure Summary (K : Type*) where
  empty : K
  one : K
  vertices : ℕ
  edges : ℕ
  deriving DecidableEq, Repr

namespace Summary

variable [CommSemiring K]

instance : CommMonoid (Summary K) where
  one := ⟨1, 0, 0, 0⟩
  mul x y := ⟨x.empty * y.empty, x.one * y.empty + x.empty * y.one,
    x.vertices + y.vertices, x.edges + y.edges⟩
  mul_assoc a b c := by
    apply Summary.ext
    · exact mul_assoc _ _ _
    · change (a.one * b.empty + a.empty * b.one) * c.empty +
        (a.empty * b.empty) * c.one =
        a.one * (b.empty * c.empty) + a.empty * (b.one * c.empty + b.empty * c.one)
      ring
    · exact Nat.add_assoc _ _ _
    · exact Nat.add_assoc _ _ _
  one_mul a := by
    apply Summary.ext
    · exact one_mul _
    · change 0 * a.empty + 1 * a.one = a.one
      simp
    · exact Nat.zero_add _
    · exact Nat.zero_add _
  mul_one a := by
    apply Summary.ext
    · exact mul_one _
    · change a.one * 1 + a.empty * 0 = a.one
      simp
    · exact Nat.add_zero _
    · exact Nat.add_zero _
  mul_comm a b := by
    apply Summary.ext
    · exact mul_comm _ _
    · change a.one * b.empty + a.empty * b.one = b.one * a.empty + b.empty * a.one
      ring
    · exact Nat.add_comm _ _
    · exact Nat.add_comm _ _

/-- One child contributes its two boundary messages and its original child edge. -/
def child (p : K) (t : Tree K) : Summary K :=
  ⟨t.eval.2, p * t.eval.1, t.vertices, 1 + t.edges⟩

/-- Summary of an actual forest, with no denotation enumeration. -/
def forest (ts : Forest K) : Summary K :=
  ⟨ts.eval.1, ts.eval.2, ts.vertices, ts.edges⟩

@[simp] theorem forest_nil : forest (Forest.nil : Forest K) = 1 := rfl

@[simp] theorem forest_cons (p : K) (t : Tree K) (ts : Forest K) :
    forest (.cons p t ts) = child p t * forest ts := by
  rfl

/-- Assemble a list by ordinary structural recursion. -/
def ofList {α : Type*} (port : α → K) (tree : α → Tree K) : List α → Forest K
  | [] => .nil
  | u :: us => .cons (port u) (tree u) (ofList port tree us)

@[simp] theorem forest_ofList {α : Type*} (port : α → K) (tree : α → Tree K)
    (us : List α) :
    forest (ofList port tree us) = (us.map fun u => child (port u) (tree u)).prod := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [ofList, forest_cons, ih, List.map_cons, List.prod_cons]

@[simp] theorem forest_ofFn {n : ℕ} (port : Fin n → K) (tree : Fin n → Tree K) :
    forest (Forest.ofFn port tree) = ∏ i, child (port i) (tree i) := by
  induction n with
  | zero => simp [Forest.ofFn]
  | succ n ih => simp only [Forest.ofFn, forest_cons, ih, Fin.prod_univ_succ]

/-- Sorting changes no value or count and requires no choice of a finite equivalence. -/
theorem forest_sorted {α : Type*} [Fintype α] [LinearOrder α]
    (port : α → K) (tree : α → Tree K) :
    forest (ofList port tree (Finset.univ.sort (· ≤ ·))) =
      ∏ u, child (port u) (tree u) := by
  rw [forest_ofList, ← List.prod_toFinset _ (Finset.sort_nodup _ _)]
  simp

/-- Equality of summaries is enough for either boundary value and exact size. -/
theorem node_congr (a b : K) {xs ys : Forest K} (h : forest xs = forest ys) :
    (Tree.node a b xs).eval = (Tree.node a b ys).eval ∧
    (Tree.node a b xs).vertices = (Tree.node a b ys).vertices ∧
    (Tree.node a b xs).edges = (Tree.node a b ys).edges := by
  have hp := congrArg Summary.empty h
  have hs := congrArg Summary.one h
  have hv := congrArg Summary.vertices h
  have he := congrArg Summary.edges h
  simp only [forest] at hp hs hv he
  simp only [Tree.eval, Tree.vertices, Tree.edges, hp, hs, hv, he, and_self]

end Summary
end Holant.OneHot.Computable.Evaluation
