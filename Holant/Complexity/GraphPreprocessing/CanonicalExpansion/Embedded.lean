import Holant.Complexity.GraphPreprocessing.Traversal.OriginalTree

/-! Expansion of a rooted tree whose references retain original vertex IDs in
a larger physical table. Unrelated rows need no modification or compaction. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalExpansion
open Computability Holant.Algebraic Holant.OneHot Holant.OneHot.Decomposition
open Holant.OneHot.Computable.Evaluation Holant.OneHot.StackProgram
open Traversal
variable {A : Type} {n m N : ℕ} {endpoint : Fin m → Bool → Fin n} {root : Fin n}

/-- A physical table lookup expands at its actual original reference index. -/
theorem reference_of_get (rows : List (List Bool)) (i : Fin rows.length) (row out : List Bool)
    (hrow : rows[i.val] = row) (count : ℕ) (h : Expands rows row out count) :
    Expands rows (reference i.val) out (count+1) := by
  have split : rows = rows.take i.val ++ row :: rows.drop (i.val+1) := by
    have hh := List.take_append_drop i.val rows
    rw [List.drop_eq_getElem_cons i.isLt,hrow] at hh
    exact hh.symm
  have hlen : (rows.take i.val).length = i.val := by
    simp [List.length_take]
  have href := Expands.reference (pending := []) (rows.take i.val) (rows.drop (i.val+1)) row split
    (by simpa only [List.append_nil] using h)
  simpa only [List.append_nil,hlen] using href

/-- The same literal row layout, with child references interpreted in the full
original-ID table rather than the compact component vertex range. -/
def embeddedRow (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A)
    (id : Fin n → Fin N) (closed : Bool) (v : Fin n) : List Bool :=
  literals (frame (e.encode (a v)) ++ if closed = true ∧ v = root then [] else frame (e.encode (b v))) ++
    childTasks e (fun u : Child t v => port ⟨u.val,u.property.1⟩) (fun u => id u.val) (children t v)

 theorem childTasks_flatMap {ι : Type} (e : Encoding A Bool) (port : ι → A)
    (id : ι → Fin N) (us : List ι) :
    childTasks e port id us =
      us.flatMap (fun u => literals (true::frame (e.encode (port u))) ++ reference (id u).val) ++
        literals [false] := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [childTasks,List.flatMap_cons,ih,List.append_assoc]

/-- Every ordinary subtree expands from its original reference. The only table
premise is a literal row identity, established from actual raw rows later. -/
theorem expand_embedded_build (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A) (id : Fin n → Fin N)
    (rows : List (List Bool)) (hlen : rows.length = N) (closed : Bool)
    (hrows : ∀ v, rows[(id v).val]'(hlen ▸ (id v).isLt) = embeddedRow t e a b port id closed v)
    (D : ℕ) (depthBound : ∀ u, t.depth u ≤ D) :
    ∀ fuel v, D < t.depth v+fuel → (closed = false ∨ v ≠ root) →
      Expands rows (reference (id v).val)
        (TreeEncoding.treeEncode e (build t a b port fuel v)) (build t a b port fuel v).vertices := by
  intro fuel
  induction fuel with
  | zero => intro v hv; have hd := depthBound v; omega
  | succ fuel ih =>
    intro v hv hclosed
    have childrenExpand := expand_children rows e
      (fun u : Child t v => port ⟨u.val,u.property.1⟩) (fun u => id u.val)
      (fun u => build t a b port fuel u.val) (children t v) (fun u hu =>
        ih u.val (by have hd := child_depth_lt t v u; omega) (Or.inr u.property.1))
    have hc : ¬(closed = true ∧ v = root) := by
      rintro ⟨hc,hvroot⟩
      rcases hclosed with hf | hn
      · rw [hf] at hc
        contradiction
      · exact hn hvroot
    have body := (Expands.bits rows (frame (e.encode (a v)) ++ frame (e.encode (b v)))).append childrenExpand
    have href := reference_of_get rows ⟨(id v).val,hlen ▸ (id v).isLt⟩ _ _ (hrows v) _
      (by simpa only [embeddedRow,ite_eq_right hc] using body)
    simpa only [build,TreeEncoding.treeEncode,Tree.vertices,Nat.zero_add,Nat.add_comm] using href

/-- A component-root reference in the full original table expands to the exact
closed labelled tree, omitting precisely the unused root-parent coefficient. -/
theorem expand_embedded_closed (t : RootedSpanning endpoint root) (e : Encoding A Bool)
    (a b : Fin n → A) (port : {u : Fin n // u ≠ root} → A) (id : Fin n → Fin N)
    (rows : List (List Bool)) (hlen : rows.length = N)
    (hrows : ∀ v, rows[(id v).val]'(hlen ▸ (id v).isLt) = embeddedRow t e a b port id true v)
    (D : ℕ) (depthBound : ∀ u, t.depth u ≤ D) :
    Expands rows (reference (id root).val) (closedEncode e (tree t a b port D))
      (tree t a b port D).vertices := by
  have childrenExpand := expand_children rows e
    (fun u : Child t root => port ⟨u.val,u.property.1⟩) (fun u => id u.val)
    (fun u => build t a b port D u.val) (children t root) (fun u hu =>
      expand_embedded_build t e a b port id rows hlen true hrows D depthBound D u.val
        (by have hd := child_depth_lt t root u; omega) (Or.inr u.property.1))
  have body := (Expands.bits rows (frame (e.encode (a root)))).append childrenExpand
  have href := reference_of_get rows ⟨(id root).val,hlen ▸ (id root).isLt⟩ _ _ (hrows root) _
    (by simpa [embeddedRow] using body)
  simpa only [tree,build,closedEncode,Tree.vertices,Nat.zero_add,Nat.add_comm] using href

end Holant.Complexity.GraphPreprocessing.CanonicalExpansion
