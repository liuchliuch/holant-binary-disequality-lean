import Holant.Complexity.GraphPreprocessing.Traversal.OriginalTree

/-! Explicit original-vertex bounds for actual row serialization and clean
finite-machine traversal. The fixed label length bound is family-local. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.Traversal
open Turing Computability Holant.Algebraic Holant.OneHot Holant.OneHot.Decomposition
open Holant.OneHot.Computable.Evaluation Holant.OneHot.StackProgram
variable {A : Type} {n m : ℕ} {endpoint : Fin m → Bool → Fin n} {root : Fin n}

theorem childTasks_length_le {ι : Type} (e : Encoding A Bool) (C : ℕ) (hc : ∀ a, (e.encode a).length ≤ C)
    (port : ι → A) (vertex : ι → Fin n) (us : List ι) :
    (childTasks e port vertex us).length ≤ 2+us.length*(4*C+n+5) := by
  induction us with
  | nil => simp [childTasks,literals,literal]
  | cons u us ih =>
    have hp := hc (port u)
    have hv := (vertex u).isLt
    simp only [childTasks,List.length_append,literals_length,List.length_cons,frame_length,reference_length]
    nlinarith

theorem children_length_le (t : RootedSpanning endpoint root) (v : Fin n) : (children t v).length ≤ n := by
  have h := Fintype.card_subtype_le (fun u : Fin n => u ≠ root ∧ parent t u = v)
  simpa [children] using h

theorem rowBody_length_le (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (C : ℕ) (hc : ∀ a, (e.encode a).length ≤ C) (a b : Fin n → A)
    (port : {u : Fin n // u ≠ root} → A) (closed : Bool) (v : Fin n) :
    (rowBody t e a b port closed v).length ≤ 8*C+6+(4*C+n+5)*n := by
  have hchild := childTasks_length_le e C hc (fun u : Child t v => port ⟨u.1,u.2.1⟩)
    (fun u => u.1) (children t v)
  have hlen := children_length_le t v
  have ha := hc (a v)
  have hb := hc (b v)
  unfold rowBody
  simp only [List.length_append,literals_length]
  split <;> simp only [List.length_append,frame_length,List.length_nil]
  all_goals nlinarith [Nat.mul_le_mul_right (4*C+n+5) hlen]

def rowSizeBound (C n : ℕ) : ℕ := 2*n*(8*C+6+(4*C+n+5)*n)+2*n+1

theorem tableBits_length_le (rows : List (List Bool)) (R : ℕ) (h : ∀ row ∈ rows, row.length ≤ R) :
    (tableBits rows).length ≤ 2*rows.length*R+2*rows.length+1 := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hh := h row (by simp)
    have ht := ih (fun r hr => h r (by simp [hr]))
    simp only [tableBits_cons,List.length_cons,List.length_append,frame_length]
    nlinarith

theorem originalRows_size (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (C : ℕ) (hc : ∀ a, (e.encode a).length ≤ C) (a b : Fin n → A)
    (port : {u : Fin n // u ≠ root} → A) (closed : Bool) :
    (tableBits (originalRows t e a b port closed)).length ≤ rowSizeBound C n := by
  have h := tableBits_length_le (originalRows t e a b port closed) (8*C+6+(4*C+n+5)*n) (by
    intro row hr
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr
    exact rowBody_length_le t e C hc a b port closed v)
  simpa only [originalRows_length,rowSizeBound] using h

theorem closedEncode_length_le (e : Encoding A Bool) (C : ℕ) (hc : ∀ a, (e.encode a).length ≤ C)
    (q : Holant.OneHot.Tree A) : (closedEncode e q).length ≤ (6*C+5)*q.vertices := by
  have h := TreeEncoding.treeEncode_length_le e C hc q
  have he := q.edges_add_one_eq_vertices
  have hclosed : (closedEncode e q).length ≤ (TreeEncoding.treeEncode e q).length := by
    cases q
    simp only [closedEncode,TreeEncoding.treeEncode,List.length_append]
    omega
  nlinarith

def originalClosedTime (C n : ℕ) : ℕ :=
  3*((6*C+5)*n)+n*(5*rowSizeBound C n+8)+6*rowSizeBound C n+n+10

/-- Literal original labelled prefix, produced by source-counted preparation
and the actual pointer-table machine, with every work stack erased. -/
theorem original_closed_machine (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A) (D : ℕ) (bound : ∀ u, t.depth u ≤ D) :
    ∃ time, time ≤ cleanBound (originalRows t e a b port true) (closedEncode e (tree t a b port D)) n ∧
      StackProtocol.RunsExactly preparedMachine.computer.step
        (initList preparedMachine.computer (preparedInput (originalRows t e a b port true) (reference root.val)))
        (haltList preparedMachine.computer (closedEncode e (tree t a b port D))) time := by
  have h := expand_closed t e a b port D bound
  rw [tree_vertices_original t a b port D bound] at h
  exact clean_execute_bounded h (by simp)

/-- The original-V bound is degree four; every copy, lookup, reference and
output cleanup remains charged in the finite elementary-instruction interpreter. -/
theorem original_closed_polynomial (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (C : ℕ) (hc : ∀ a, (e.encode a).length ≤ C) (a b : Fin n → A)
    (port : {u : Fin n // u ≠ root} → A) (D : ℕ) (bound : ∀ u, t.depth u ≤ D) :
    ∃ time, time ≤ originalClosedTime C n ∧
      (Primitive.run program time
        (some (initList preparedMachine.computer (preparedInput (originalRows t e a b port true) (reference root.val))))).2 =
        some (haltList preparedMachine.computer (closedEncode e (tree t a b port D))) ∧
      (Primitive.run program time
        (some (initList preparedMachine.computer (preparedInput (originalRows t e a b port true) (reference root.val))))).1 ≤
        8*originalClosedTime C n := by
  obtain ⟨time,ht,run⟩ := original_closed_machine t e a b port D bound
  have hr := originalRows_size t e C hc a b port true
  have ho := closedEncode_length_le e C hc (tree t a b port D)
  rw [tree_vertices_original t a b port D bound] at ho
  have hh : cleanBound (originalRows t e a b port true) (closedEncode e (tree t a b port D)) n ≤ originalClosedTime C n := by
    unfold cleanBound originalClosedTime
    rw [originalRows_length]
    nlinarith [Nat.mul_le_mul_left n (show 5*(tableBits (originalRows t e a b port true)).length+8 ≤ 5*rowSizeBound C n+8 by omega)]
  have cost := Primitive.execution_cost program 8 program_budget _ _ _ run
  exact ⟨time,le_trans ht hh,cost.1,le_trans cost.2 (Nat.mul_le_mul_left 8 (le_trans ht hh))⟩

end Holant.Complexity.GraphPreprocessing.Traversal
