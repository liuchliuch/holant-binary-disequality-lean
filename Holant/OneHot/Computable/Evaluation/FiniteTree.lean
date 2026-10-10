import Holant.OneHot.Computable.Evaluation.Fold

/-!
# Executable finite-index construction of a rooted tree

Children are scanned in increasing original vertex ID order. The fuel is an
explicit bound on the computed rank, not an input recursive decomposition.
Classical semantic enumeration occurs only in proof statements and proofs.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Computable.Evaluation

open Holant.OneHot.Decomposition

variable {n m : ℕ} {endpoint : Fin m → Bool → Fin n} {root : Fin n}
variable (t : RootedSpanning endpoint root)

/-- Finite equality makes the existing total parent function executable. -/
def parent (v : Fin n) : Fin n :=
  if h : v = root then root else endpoint (t.parentEnd ⟨v, h⟩).1 (!(t.parentEnd ⟨v, h⟩).2)

theorem parent_eq (v : Fin n) : parent t v = t.parent v := by
  unfold parent RootedSpanning.parent
  split <;> rfl

/-- A decidable original-index child predicate. -/
abbrev Child (v : Fin n) := {u : Fin n // u ≠ root ∧ parent t u = v}

/-- The order is the inherited original vertex order. -/
def children (v : Fin n) : List (Child t v) := Finset.univ.sort (· ≤ ·)

@[simp] theorem mem_children (v : Fin n) (u : Child t v) : u ∈ children t v := by
  simp [children]

@[simp] theorem children_nodup (v : Fin n) : (children t v).Nodup :=
  Finset.sort_nodup _ _

/-- Child identities are the original vertices, with exactly the same parent edge. -/
def childEquiv (v : Fin n) : Child t v ≃ t.Child v where
  toFun u := ⟨u.1, u.2.1, (parent_eq t u.1).symm.trans u.2.2⟩
  invFun u := ⟨u.1, u.2.1, (parent_eq t u.1).trans u.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem child_depth_lt (v : Fin n) (u : Child t v) : t.depth v < t.depth u.1 := by
  have h := t.parent_depth_lt ⟨u.1, u.2.1⟩
  have hp : endpoint (t.parentEnd ⟨u.1, u.2.1⟩).1
      (!(t.parentEnd ⟨u.1, u.2.1⟩).2) = v := by
    simpa only [parent, dite_eq_right u.2.1] using u.2.2
  rw [hp] at h
  exact h

variable {K : Type*} [CommSemiring K]

/-- Ordinary bounded recursion, with literal finite lists of original children. -/
def build (a b : Fin n → K) (port : {u : Fin n // u ≠ root} → K) :
    ℕ → Fin n → Tree K
  | 0, v => .node (a v) (b v) .nil
  | fuel + 1, v => .node (a v) (b v)
      (Summary.ofList (fun u : Child t v => port ⟨u.1, u.2.1⟩)
        (fun u => build a b port fuel u.1) (children t v))

/-- Complete fuel yields the semantic value and exact represented size. The
semantic tree is used only to verify the executed construction, never to run it. -/
theorem build_spec (a b : Fin n → K) (port : {u : Fin n // u ≠ root} → K)
    (maxDepth : ℕ) (bound : ∀ u, t.depth u ≤ maxDepth) :
    ∀ fuel v, maxDepth < t.depth v + fuel →
      (build t a b port fuel v).eval = (t.unfold a b port v).tree.eval ∧
      (build t a b port fuel v).vertices = (t.unfold a b port v).tree.vertices ∧
      (build t a b port fuel v).edges = (t.unfold a b port v).tree.edges := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro v hv
    have hh := bound v
    omega
  | succ fuel ih =>
    intro v hv
    rw [build, RootedSpanning.unfold]
    apply Summary.node_congr
    change Summary.forest (Summary.ofList _ _ (Finset.univ.sort (· ≤ ·))) =
      Summary.forest (Forest.ofFn _ _)
    rw [Summary.forest_sorted, Summary.forest_ofFn]
    let e := (childEquiv t v).trans (Fintype.equivFin (t.Child v))
    rw [← e.prod_comp]
    apply Finset.prod_congr rfl
    intro u _
    have hu : maxDepth < t.depth u.1 + fuel := by
      have hd := child_depth_lt t v u
      omega
    rcases ih u.1 hu with ⟨hval, hverts, hedges⟩
    calc
      _ = Summary.child (port ⟨u.1, u.2.1⟩) (t.unfold a b port u.1).tree := by
        simp only [Summary.child, hval, hverts, hedges]
      _ = _ := (congrArg (fun w : t.Child v =>
          Summary.child (port ⟨w.1, w.2.1⟩) (t.unfold a b port w.1).tree)
        ((Fintype.equivFin (t.Child v)).symm_apply_apply ((childEquiv t v) u))).symm

/-- One plus the proved maximum rank includes all leaves. -/
def tree (a b : Fin n → K) (port : {u : Fin n // u ≠ root} → K)
    (maxDepth : ℕ) : Tree K := build t a b port (maxDepth + 1) root

theorem tree_spec (a b : Fin n → K) (port : {u : Fin n // u ≠ root} → K)
    (maxDepth : ℕ) (bound : ∀ u, t.depth u ≤ maxDepth) :
    (tree t a b port maxDepth).eval = (t.unfold a b port root).tree.eval ∧
    (tree t a b port maxDepth).vertices = n ∧
    (tree t a b port maxDepth).edges + 1 = n := by
  have h := build_spec t a b port maxDepth bound (maxDepth + 1) root (by omega)
  refine ⟨h.1, ?_, ?_⟩
  · exact h.2.1.trans (by simpa using t.unfold_vertices a b port)
  · change (build t a b port (maxDepth + 1) root).edges + 1 = n
    rw [h.2.2]
    simpa using t.unfold_edges_add_one a b port

/-- The closed-root program's first result is its unoccupied boundary value. -/
theorem closedProgram_run (q : Tree K) :
    q.closedProgram.run = (q.eval.1, 3 * q.vertices + 5 * q.edges - 1) := by
  rw [Tree.closedProgram_network_spec, Tree.denote_closedNetwork, Tree.eval_correct]

end Holant.OneHot.Computable.Evaluation
