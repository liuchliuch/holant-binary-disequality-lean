import Holant.OneHot.Decomposition.Descendants
import Holant.OneHot.Decomposition.ForestAssembly
import Holant.OneHot.NetworkBridge.Geometry

/-!
# Unfolding extracted parent trees into the verified recursive datatype

Every recursive call descends to a strictly smaller, proved descendant set.
The resulting `Tree` has an explicit bijection from its actual node addresses
to the original vertices. Coefficients are read from supplied original-vertex
and original-parent-edge tables; this construction does not assert the final
ordered-port network isomorphism or any extraction runtime bound.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Decomposition.RootedSpanning

variable {V E K : Type*} {endpoint : E → Bool → V} {root : V}
variable (t : RootedSpanning endpoint root) [Fintype V]

open scoped Classical

/-- An actual recursive tree together with an exact original-vertex enumeration. -/
structure TreeEnumeration (K : Type*) (v : V) where
  tree : Tree K
  vertices : tree.Vertex ≃ t.Descendant v
  root_vertex : (vertices tree.rootVertex).1 = v

/-- Extract each node and every child from the genuine parent structure.
The child order is the fixed finite enumeration and is exposed by the address
bijection; original port order will be related by an explicit local equivalence. -/
noncomputable def unfold (a b : V → K) (port : {v : V // v ≠ root} → K)
    (v : V) : t.TreeEnumeration K v := by
  let children := Fintype.equivFin (t.Child v)
  let subtrees (u : t.Child v) := unfold a b port u.1
  let childTrees (i : Fin (Fintype.card (t.Child v))) := (subtrees (children.symm i)).tree
  let childPorts (i : Fin (Fintype.card (t.Child v))) :=
    port ⟨(children.symm i).1, (children.symm i).2.1⟩
  let forest := Forest.ofFn childPorts childTrees
  let forestVertices : forest.Vertex ≃ (Σ u : t.Child v, t.Descendant u.1) :=
    (Forest.ofFnVertex childPorts childTrees).trans
      ((Equiv.sigmaCongrRight (fun i => (subtrees (children.symm i)).vertices)).trans
        (Equiv.sigmaCongrLeft (β := fun u : t.Child v => t.Descendant u.1) children.symm))
  exact {
    tree := .node (a v) (b v) forest
    vertices := (Equiv.sumCongr (Equiv.refl Unit) forestVertices).trans (t.descendantSplit v)
    root_vertex := rfl }
termination_by Fintype.card (t.Descendant v)
decreasing_by exact t.descendant_card_child_lt _ _

/-- The extracted root tree contains every original graph vertex exactly once. -/
noncomputable def unfoldVertices (a b : V → K) (port : {v : V // v ≠ root} → K) :
    (t.unfold a b port root).tree.Vertex ≃ V :=
  (t.unfold a b port root).vertices.trans t.rootDescendantEquiv

/-- Exact node count of the generated existing `Tree` datatype. -/
theorem unfold_vertices (a b : V → K) (port : {v : V // v ≠ root} → K) :
    (t.unfold a b port root).tree.vertices = Fintype.card V := by
  rw [← Tree.card_vertex]
  exact Fintype.card_congr (t.unfoldVertices a b port)

/-- The generated existing `Tree` has exactly one fewer child edges than vertices. -/
theorem unfold_edges_add_one (a b : V → K) (port : {v : V // v ≠ root} → K) :
    (t.unfold a b port root).tree.edges + 1 = Fintype.card V := by
  rw [Tree.edges_add_one_eq_vertices, t.unfold_vertices]

@[simp] theorem unfoldVertices_root (a b : V → K) (port : {v : V // v ≠ root} → K) :
    t.unfoldVertices a b port (t.unfold a b port root).tree.rootVertex = root :=
  (t.unfold a b port root).root_vertex

/-- Each unfolded node retains its own original zero-word coefficient. -/
theorem unfold_zeroCoefficient (a b : V → K) (port : {v : V // v ≠ root} → K)
    (v : V) : ∀ x : (t.unfold a b port v).tree.Vertex,
    (t.unfold a b port v).tree.zeroCoefficient x =
      a ((t.unfold a b port v).vertices x).1 := by
  induction v using (measure (fun v => Fintype.card (t.Descendant v))).wf.induction with
  | h v ih =>
    rw [unfold]
    intro x
    rcases x with u | x
    · cases u; rfl
    · rw [Tree.zeroCoefficient, Forest.zeroCoefficient_ofFn]
      apply ih
      exact t.descendant_card_child_lt _ _

/-- Every unfolded node has precisely its parent port followed by all genuine
child ports. The separate closed-root constructor removes the virtual root port. -/
theorem unfold_arity (a b : V → K) (port : {v : V // v ≠ root} → K)
    (v : V) : ∀ x : (t.unfold a b port v).tree.Vertex,
    (t.unfold a b port v).tree.arity x =
      Fintype.card (t.Child ((t.unfold a b port v).vertices x).1) + 1 := by
  induction v using (measure (fun v => Fintype.card (t.Descendant v))).wf.induction with
  | h v ih =>
    rw [unfold]
    intro x
    rcases x with u | x
    · cases u
      exact congrArg (· + 1) (Forest.length_ofFn _ _)
    · rw [Tree.arity, Forest.arity_ofFn]
      apply ih
      exact t.descendant_card_child_lt _ _

/-- The singleton coefficients of every actual unfolded node retain the original
parent coefficient and all original child-edge coefficients in enumeration order. -/
private theorem unfold_portCoefficient_aux (a b : V → K) (port : {v : V // v ≠ root} → K)
    (v : V) : ∀ (x : (t.unfold a b port v).tree.Vertex)
      (i : Fin ((t.unfold a b port v).tree.arity x))
      (h : (t.unfold a b port v).tree.arity x =
        Fintype.card (t.Child ((t.unfold a b port v).vertices x).1) + 1),
    (t.unfold a b port v).tree.portCoefficient x i =
      Fin.cons (α := fun _ => K) (b ((t.unfold a b port v).vertices x).1)
        (fun j => let u := (Fintype.equivFin (t.Child ((t.unfold a b port v).vertices x).1)).symm j
          port ⟨u.1, u.2.1⟩) (Fin.cast h i) := by
  induction v using (measure (fun v => Fintype.card (t.Descendant v))).wf.induction with
  | h v ih =>
    rw [unfold]
    intro x i ha
    rcases x with u | x
    · cases u
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        change (Forest.ofFn _ _).coefficients i = _
        rw [Forest.coefficients_ofFn]
        rfl
    · rw [Tree.portCoefficient, Forest.portCoefficient_ofFn]
      apply ih
      · exact t.descendant_card_child_lt _ _
      · exact t.unfold_arity _ _ _ _ _

/-- Parent/child singleton table of every original unfolded vertex. -/
theorem unfold_portCoefficient (a b : V → K) (port : {v : V // v ≠ root} → K)
    (v : V) (x : (t.unfold a b port v).tree.Vertex)
    (i : Fin ((t.unfold a b port v).tree.arity x)) :
    (t.unfold a b port v).tree.portCoefficient x i =
      Fin.cons (α := fun _ => K) (b ((t.unfold a b port v).vertices x).1)
        (fun j => let u := (Fintype.equivFin (t.Child ((t.unfold a b port v).vertices x).1)).symm j
          port ⟨u.1, u.2.1⟩) (Fin.cast (t.unfold_arity a b port v x) i) :=
  t.unfold_portCoefficient_aux a b port v x i _

end Holant.OneHot.Decomposition.RootedSpanning
