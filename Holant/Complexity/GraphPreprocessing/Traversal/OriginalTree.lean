import Holant.Complexity.GraphPreprocessing.Traversal.PreparedBounds
import Holant.OneHot.StackProgram.TreeEncoding
import Holant.OneHot.StackProgram.GraphLabels
import Holant.OneHot.StackProgram.Bounds

/-! Reconstructed literal original-ID row correspondence. Rows preserve the
existing increasing child order and original coefficient labels; closed roots
omit precisely their unused parent coefficient. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.Traversal
open Turing Computability Holant.Algebraic Holant.OneHot Holant.OneHot.Decomposition
open Holant.OneHot.Computable.Evaluation Holant.OneHot.StackProgram
variable {A : Type} {n m : ℕ} {endpoint : Fin m → Bool → Fin n} {root : Fin n}

/-- Every pointer contains its actual original vertex position. -/
def childTasks {ι : Type} (e : Encoding A Bool) (port : ι → A) (vertex : ι → Fin n) : List ι → List Bool
  | [] => literals [false]
  | u::us => literals (true::frame (e.encode (port u))) ++ reference (vertex u).val ++ childTasks e port vertex us

def rowBody (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A) (closed : Bool) (v : Fin n) : List Bool :=
  literals (frame (e.encode (a v)) ++ if closed = true ∧ v = root then [] else frame (e.encode (b v))) ++
    childTasks e (fun u : Child t v => port ⟨u.1,u.2.1⟩) (fun u => u.1) (children t v)

def originalRows (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A) (closed : Bool) : List (List Bool) :=
  List.ofFn (rowBody t e a b port closed)

@[simp] theorem originalRows_length (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A) (closed : Bool) :
    (originalRows t e a b port closed).length = n := by simp [originalRows]

theorem original_reference (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A) (closed : Bool) (v : Fin n)
    (out : List Bool) (count : ℕ)
    (h : Expands (originalRows t e a b port closed) (rowBody t e a b port closed v) out count) :
    Expands (originalRows t e a b port closed) (reference v.val) out (count+1) := by
  let rows := originalRows t e a b port closed
  have hv : v.val < rows.length := by simpa [rows] using v.isLt
  have row : rows[v.val] = rowBody t e a b port closed v := by simp [rows,originalRows]
  have split : rows = rows.take v.val ++ rowBody t e a b port closed v :: rows.drop (v.val+1) := by
    have hsplit := List.take_append_drop v.val rows
    rw [List.drop_eq_getElem_cons hv,row] at hsplit
    exact hsplit.symm
  have hlen : (rows.take v.val).length = v.val := by simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hv)]
  have href := Expands.reference (pending := []) (rows.take v.val) (rows.drop (v.val+1))
    (rowBody t e a b port closed v) split (by simpa only [List.append_nil] using h)
  simpa only [List.append_nil,hlen] using href

theorem expand_children {ι : Type} (rows : List (List Bool)) (e : Encoding A Bool)
    (port : ι → A) (vertex : ι → Fin n) (trees : ι → Holant.OneHot.Tree A) (us : List ι)
    (h : ∀ u ∈ us, Expands rows (reference (vertex u).val) (TreeEncoding.treeEncode e (trees u)) (trees u).vertices) :
    Expands rows (childTasks e port vertex us)
      (TreeEncoding.forestEncode e (Summary.ofList port trees us)) (Summary.ofList port trees us).vertices := by
  induction us with
  | nil => exact Expands.bits rows [false]
  | cons u us ih =>
    have tail := ih (fun v hv => h v (by simp [hv]))
    have head := h u (by simp)
    have whole := ((Expands.bits rows (true::frame (e.encode (port u)))).append head).append tail
    simpa only [childTasks,Summary.ofList,TreeEncoding.forestEncode,Forest.vertices,Nat.zero_add,
      List.append_assoc,List.cons_append] using whole

/-- Sufficient rank fuel expands the literal original tree, not just a tree with
an equal semantic value. References count exactly its represented vertices. -/
theorem expand_build (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A) (closed : Bool)
    (D : ℕ) (depthBound : ∀ u, t.depth u ≤ D) :
    ∀ fuel v, D < t.depth v+fuel → (closed = false ∨ v ≠ root) →
      Expands (originalRows t e a b port closed) (reference v.val)
        (TreeEncoding.treeEncode e (build t a b port fuel v)) (build t a b port fuel v).vertices := by
  intro fuel
  induction fuel with
  | zero => intro v hv; have hd := depthBound v; omega
  | succ fuel ih =>
    intro v hv hclosed
    have childrenExpand := expand_children (originalRows t e a b port closed) e
      (fun u : Child t v => port ⟨u.1,u.2.1⟩) (fun u => u.1)
      (fun u => build t a b port fuel u.1) (children t v) (fun u hu =>
        ih u.1 (by have hd := child_depth_lt t v u; omega) (Or.inr u.2.1))
    have hc : ¬(closed = true ∧ v = root) := by
      rintro ⟨hc,hvroot⟩
      rcases hclosed with hf | hn
      · rw [hf] at hc
        contradiction
      · exact hn hvroot
    have body := (Expands.bits (originalRows t e a b port closed)
      (frame (e.encode (a v)) ++ frame (e.encode (b v)))).append childrenExpand
    have href := original_reference t e a b port closed v _ _
      (by simpa only [rowBody,if_neg hc] using body)
    simpa only [build,TreeEncoding.treeEncode,Tree.vertices,Nat.zero_add,Nat.add_comm] using href

def closedEncode (e : Encoding A Bool) : Holant.OneHot.Tree A → List Bool
  | .node a _ ts => frame (e.encode a) ++ TreeEncoding.forestEncode e ts

/-- Closed roots have no virtual parent port and retain their original root label. -/
theorem expand_closed (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A)
    (D : ℕ) (depthBound : ∀ u, t.depth u ≤ D) :
    Expands (originalRows t e a b port true) (reference root.val)
      (closedEncode e (tree t a b port D)) (tree t a b port D).vertices := by
  have childrenExpand := expand_children (originalRows t e a b port true) e
    (fun u : Child t root => port ⟨u.1,u.2.1⟩) (fun u => u.1)
    (fun u => build t a b port D u.1) (children t root) (fun u hu =>
      expand_build t e a b port true D depthBound D u.1
        (by have hd := child_depth_lt t root u; omega) (Or.inr u.2.1))
  have body := (Expands.bits (originalRows t e a b port true) (frame (e.encode (a root)))).append childrenExpand
  have href := original_reference t e a b port true root _ _
    (by simpa [rowBody] using body)
  simpa only [tree,build,closedEncode,Tree.vertices,Nat.zero_add,Nat.add_comm] using href

/-- Label interpretation is used only to recover the already proved exact count. -/
theorem tree_vertices_original (t : RootedSpanning endpoint root)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A)
    (D : ℕ) (depthBound : ∀ u, t.depth u ≤ D) : (tree t a b port D).vertices = n := by
  have h := (tree_spec t (fun _ => (0 : ℕ)) (fun _ => (0 : ℕ)) (fun _ => (0 : ℕ)) D depthBound).2.1
  have hi := interpret_build t (fun _ : A => (0 : ℕ)) a b port (D+1) root
  have hv := congrArg Tree.vertices hi
  rw [interpretTree_vertices] at hv
  exact hv.trans h

end Holant.Complexity.GraphPreprocessing.Traversal
