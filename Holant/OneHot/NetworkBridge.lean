import Holant.OneHot.Tree
import Holant.OneHot.NetworkBridge.Table
import Holant.OneHot.NetworkBridge.FiniteNative
import Holant.NetworkGluing.Finite
import Holant.Support
import Mathlib.Data.Fintype.Sum

/-!
# The actual native-X network of an ordered one-hot tree

Vertices are node addresses, edges are child addresses, and the root's parent
port is the unique ordinary boundary. The true end of every edge is its parent
endpoint. All local port numbers and all coefficients are retained.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot

variable {K : Type*}

mutual
def Tree.Vertex : Tree K → Type
  | .node _ _ ts => Unit ⊕ ts.Vertex
def Forest.Vertex : Forest K → Type
  | .nil => Empty
  | .cons _ t ts => t.Vertex ⊕ ts.Vertex
end

mutual
def Tree.Edge : Tree K → Type
  | .node _ _ ts => ts.Edge
def Forest.Edge : Forest K → Type
  | .nil => Empty
  | .cons _ t ts => Unit ⊕ (t.Edge ⊕ ts.Edge)
end

mutual
@[instance_reducible] def Tree.vertexFintype : (t : Tree K) → Fintype t.Vertex
  | .node _ _ ts =>
    letI := ts.vertexFintype
    inferInstanceAs (Fintype (Unit ⊕ ts.Vertex))
@[instance_reducible] def Forest.vertexFintype : (ts : Forest K) → Fintype ts.Vertex
  | .nil => inferInstanceAs (Fintype Empty)
  | .cons _ t ts =>
    letI := t.vertexFintype
    letI := ts.vertexFintype
    inferInstanceAs (Fintype (t.Vertex ⊕ ts.Vertex))
end

mutual
@[instance_reducible] def Tree.edgeFintype : (t : Tree K) → Fintype t.Edge
  | .node _ _ ts => ts.edgeFintype
@[instance_reducible] def Forest.edgeFintype : (ts : Forest K) → Fintype ts.Edge
  | .nil => inferInstanceAs (Fintype Empty)
  | .cons _ t ts =>
    letI := t.edgeFintype
    letI := ts.edgeFintype
    inferInstanceAs (Fintype (Unit ⊕ (t.Edge ⊕ ts.Edge)))
end

instance (t : Tree K) : Fintype t.Vertex := t.vertexFintype
instance (ts : Forest K) : Fintype ts.Vertex := ts.vertexFintype
instance (t : Tree K) : Fintype t.Edge := t.edgeFintype
instance (ts : Forest K) : Fintype ts.Edge := ts.edgeFintype

mutual
def Tree.arity : (t : Tree K) → t.Vertex → ℕ
  | .node _ _ ts, .inl _ => ts.length + 1
  | .node _ _ ts, .inr v => ts.arity v
def Forest.arity : (ts : Forest K) → ts.Vertex → ℕ
  | .nil, v => nomatch v
  | .cons _ t _, .inl v => t.arity v
  | .cons _ _ ts, .inr v => ts.arity v
end

abbrev Tree.Occurrence (t : Tree K) := (v : t.Vertex) × Fin (t.arity v)
abbrev Forest.Occurrence (ts : Forest K) := (v : ts.Vertex) × Fin (ts.arity v)

mutual
/-- Explicit occurrence-to-endpoint incidence. The boundary is root port zero. -/
def Tree.portMap : (t : Tree K) → t.Occurrence → Fin 1 ⊕ (t.Edge × Bool)
  | .node _ _ ts, ⟨.inl _, i⟩ =>
    Fin.cases (.inl 0) (fun j => .inr (ts.portMap (.inl j))) i
  | .node _ _ ts, ⟨.inr v, i⟩ => .inr (ts.portMap (.inr ⟨v, i⟩))
/-- The extra `Fin length` ports belong to the forest's common parent. -/
def Forest.portMap : (ts : Forest K) →
    Fin ts.length ⊕ ts.Occurrence → ts.Edge × Bool
  | .nil, .inl i => Fin.elim0 i
  | .nil, .inr ⟨v, _⟩ => nomatch v
  | .cons _ _t ts, .inl i => Fin.cases (.inl (), true)
      (fun j => let q := ts.portMap (.inl j); (.inr (.inr q.1), q.2)) i
  | .cons _ t _ts, .inr ⟨.inl v, i⟩ =>
      match t.portMap ⟨v, i⟩ with
      | .inl _ => (.inl (), false)
      | .inr q => (.inr (.inl q.1), q.2)
  | .cons _ _t ts, .inr ⟨.inr v, i⟩ =>
      let q := ts.portMap (.inr ⟨v, i⟩); (.inr (.inr q.1), q.2)
end

mutual
def Tree.portInv : (t : Tree K) → Fin 1 ⊕ (t.Edge × Bool) → t.Occurrence
  | .node _ _ ts, .inl _ => ⟨.inl (), (0 : Fin (ts.length + 1))⟩
  | .node _ _ ts, .inr q =>
    match ts.portInv q with
    | .inl j => ⟨.inl (), j.succ⟩
    | .inr ⟨v, i⟩ => ⟨.inr v, i⟩
def Forest.portInv : (ts : Forest K) →
    ts.Edge × Bool → Fin ts.length ⊕ ts.Occurrence
  | .nil, ⟨e, _⟩ => nomatch e
  | .cons _ _ ts, (.inl _, true) => .inl (0 : Fin (ts.length + 1))
  | .cons _ t _, (.inl _, false) =>
    let q := t.portInv (.inl 0); .inr ⟨.inl q.1, q.2⟩
  | .cons _ t _, (.inr (.inl e), b) =>
    let q := t.portInv (.inr (e, b)); .inr ⟨.inl q.1, q.2⟩
  | .cons _ _ ts, (.inr (.inr e), b) =>
    match ts.portInv (e, b) with
    | .inl j => .inl j.succ
    | .inr ⟨v, i⟩ => .inr ⟨.inr v, i⟩
end

mutual
theorem Tree.portInv_map (t : Tree K) (p : t.Occurrence) :
    t.portInv (t.portMap p) = p := by
  cases t with
  | node a b ts =>
    rcases p with ⟨v, i⟩
    cases v with
    | inl u =>
      cases u
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [Tree.portMap, Fin.cases_succ, Tree.portInv,
          Forest.portInv_map]
    | inr v => simp only [Tree.portMap, Tree.portInv, Forest.portInv_map]
theorem Forest.portInv_map (ts : Forest K) (p : Fin ts.length ⊕ ts.Occurrence) :
    ts.portInv (ts.portMap p) = p := by
  cases ts with
  | nil => cases p with
    | inl i => exact Fin.elim0 i
    | inr p => exact Empty.elim p.1
  | cons c t ts =>
    cases p with
    | inl i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [Forest.portMap, Fin.cases_succ]
        generalize h : ts.portMap (.inl j) = q
        have hq := ts.portInv_map (.inl j)
        rw [h] at hq
        rcases q with ⟨e, b⟩
        simp only [Forest.portInv, hq]
    | inr p =>
      rcases p with ⟨v, i⟩
      cases v with
      | inl v =>
        simp only [Forest.portMap]
        generalize h : t.portMap ⟨v, i⟩ = q
        have hq := t.portInv_map ⟨v, i⟩
        rw [h] at hq
        cases q with
        | inl j =>
          have hj : j = 0 := Subsingleton.elim _ _
          subst j
          simpa only [Forest.portInv] using congrArg
            (fun z : t.Occurrence => (Sum.inr ⟨Sum.inl z.1, z.2⟩ :
              Fin (Forest.cons c t ts).length ⊕ (Forest.cons c t ts).Occurrence)) hq
        | inr q =>
          simpa only [Forest.portInv] using congrArg
            (fun z : t.Occurrence => (Sum.inr ⟨Sum.inl z.1, z.2⟩ :
              Fin (Forest.cons c t ts).length ⊕ (Forest.cons c t ts).Occurrence)) hq
      | inr v =>
        simp only [Forest.portMap]
        generalize h : ts.portMap (.inr ⟨v, i⟩) = q
        have hq := ts.portInv_map (.inr ⟨v, i⟩)
        rw [h] at hq
        rcases q with ⟨e, b⟩
        simp only [Forest.portInv, hq]
end

mutual
theorem Tree.portMap_inv (t : Tree K) (q : Fin 1 ⊕ (t.Edge × Bool)) :
    t.portMap (t.portInv q) = q := by
  cases t with
  | node a b ts =>
    cases q with
    | inl j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
    | inr q =>
      simp only [Tree.portInv]
      generalize h : ts.portInv q = p
      have hp := ts.portMap_inv q
      rw [h] at hp
      cases p with
      | inl j => simp only [Tree.portMap, Fin.cases_succ, hp]
      | inr p => simp only [Tree.portMap, hp]
theorem Forest.portMap_inv (ts : Forest K) (q : ts.Edge × Bool) :
    ts.portMap (ts.portInv q) = q := by
  cases ts with
  | nil => exact Empty.elim q.1
  | cons c t ts =>
    rcases q with ⟨e, b⟩
    cases e with
    | inl u =>
      cases u
      cases b
      · simp only [Forest.portInv, Forest.portMap, Tree.portMap_inv]
      · rfl
    | inr e =>
      cases e with
      | inl e => simp only [Forest.portInv, Forest.portMap, Tree.portMap_inv]
      | inr e =>
        simp only [Forest.portInv]
        generalize h : ts.portInv (e, b) = p
        have hp := ts.portMap_inv (e, b)
        rw [h] at hp
        cases p with
        | inl j => simp only [Forest.portMap, Fin.cases_succ, hp]
        | inr p => simp only [Forest.portMap, hp]
end

/-- A proved bijection: no missing, duplicated, or dangling port occurrences. -/
def Tree.portEquiv (t : Tree K) : t.Occurrence ≃ (Fin 1 ⊕ (t.Edge × Bool)) where
  toFun := t.portMap
  invFun := t.portInv
  left_inv := t.portInv_map
  right_inv := t.portMap_inv

mutual
/-- Convert recursive choices to one Boolean for each actual native edge. -/
def Tree.edgeChoices : (t : Tree K) → t.Choice → (t.Edge → Bool)
  | .node _ _ ts, x => ts.edgeChoices x
def Forest.edgeChoices : (ts : Forest K) → ts.Choice → (ts.Edge → Bool)
  | .nil, _, e => nomatch e
  | .cons _ _ _, x, .inl _ => x.1
  | .cons _ t _, x, .inr (.inl e) => t.edgeChoices x.2.1 e
  | .cons _ _ ts, x, .inr (.inr e) => ts.edgeChoices x.2.2 e
end

mutual
def Tree.fromEdgeChoices : (t : Tree K) → (t.Edge → Bool) → t.Choice
  | .node _ _ ts, c => ts.fromEdgeChoices c
def Forest.fromEdgeChoices : (ts : Forest K) → (ts.Edge → Bool) → ts.Choice
  | .nil, _ => ()
  | .cons _ t ts, c =>
    (c (.inl ()), t.fromEdgeChoices (fun e => c (.inr (.inl e))),
      ts.fromEdgeChoices (fun e => c (.inr (.inr e))))
end

mutual
@[simp] theorem Tree.fromEdgeChoices_edgeChoices (t : Tree K) (x : t.Choice) :
    t.fromEdgeChoices (t.edgeChoices x) = x := by
  cases t with
  | node a b ts => exact ts.fromEdgeChoices_edgeChoices x
@[simp] theorem Forest.fromEdgeChoices_edgeChoices (ts : Forest K) (x : ts.Choice) :
    ts.fromEdgeChoices (ts.edgeChoices x) = x := by
  cases ts with
  | nil => exact @Subsingleton.elim Unit _ _ _
  | cons p t ts =>
    rcases x with ⟨b, x, y⟩
    simp only [Forest.fromEdgeChoices, Forest.edgeChoices,
      Tree.fromEdgeChoices_edgeChoices, Forest.fromEdgeChoices_edgeChoices]
end

mutual
@[simp] theorem Tree.edgeChoices_fromEdgeChoices (t : Tree K) (c : t.Edge → Bool) :
    t.edgeChoices (t.fromEdgeChoices c) = c := by
  cases t with
  | node a b ts => exact ts.edgeChoices_fromEdgeChoices c
@[simp] theorem Forest.edgeChoices_fromEdgeChoices (ts : Forest K) (c : ts.Edge → Bool) :
    ts.edgeChoices (ts.fromEdgeChoices c) = c := by
  cases ts with
  | nil => funext e; exact Empty.elim e
  | cons p t ts =>
    funext e
    cases e with
    | inl u => cases u; rfl
    | inr e =>
      cases e with
      | inl e =>
        exact congrFun (t.edgeChoices_fromEdgeChoices (fun e => c (.inr (.inl e)))) e
      | inr e =>
        exact congrFun (ts.edgeChoices_fromEdgeChoices (fun e => c (.inr (.inr e)))) e
end

/-- A genuine bijection between the evaluator's choices and the graph's edges. -/
def Tree.choiceEquiv (t : Tree K) : t.Choice ≃ (t.Edge → Bool) where
  toFun := t.edgeChoices
  invFun := t.fromEdgeChoices
  left_inv := t.fromEdgeChoices_edgeChoices
  right_inv := t.edgeChoices_fromEdgeChoices

mutual
theorem Tree.card_vertex (t : Tree K) : Fintype.card t.Vertex = t.vertices := by
  cases t with
  | node a b ts =>
    change Fintype.card (Unit ⊕ ts.Vertex) = 1 + ts.vertices
    simp [ts.card_vertex]
theorem Forest.card_vertex (ts : Forest K) : Fintype.card ts.Vertex = ts.vertices := by
  cases ts with
  | nil => exact Fintype.card_empty
  | cons p t ts =>
    change Fintype.card (t.Vertex ⊕ ts.Vertex) = t.vertices + ts.vertices
    simp [t.card_vertex, ts.card_vertex]
end

mutual
theorem Tree.card_edge (t : Tree K) : Fintype.card t.Edge = t.edges := by
  cases t with
  | node a b ts => exact ts.card_edge
theorem Forest.card_edge (ts : Forest K) : Fintype.card ts.Edge = ts.edges := by
  cases ts with
  | nil => exact Fintype.card_empty
  | cons p t ts =>
    change Fintype.card (Unit ⊕ (t.Edge ⊕ ts.Edge)) = 1 + t.edges + ts.edges
    simp [t.card_edge, ts.card_edge, Nat.add_assoc]
end

/-- Ordered child-port coefficients at their common parent. -/
def Forest.coefficients : (ts : Forest K) → Fin ts.length → K
  | .nil => Fin.elim0
  | .cons p _ ts => Fin.cons p ts.coefficients

/-- Ordered child endpoint bits at their common parent. -/
def Forest.selection : (ts : Forest K) → ts.Choice → Fin ts.length → Bool
  | .nil, _ => Fin.elim0
  | .cons _ _ ts, x => Fin.cons x.1 (ts.selection x.2.2)

theorem Forest.weight_selection (ts : Forest K) (x : ts.Choice) :
    Holant.weight (ts.selection x) = ts.occupied x := by
  cases ts with
  | nil => simp [Holant.weight, Forest.selection, Forest.occupied, Forest.length]
  | cons p t ts =>
    rcases x with ⟨b, x, y⟩
    change (∑ i : Fin (ts.length + 1), if (Fin.cons (α := fun _ => Bool) b (ts.selection y) i : Bool) then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact congrArg ((if b then 1 else 0) + ·) (ts.weight_selection y)

variable [CommSemiring K]

theorem Forest.prod_selection (ts : Forest K) (x : ts.Choice) :
    (∏ i, if ts.selection x i then ts.coefficients i else 1) = ts.ports x := by
  cases ts with
  | nil => simp [Forest.length, Forest.ports]
  | cons p t ts =>
    rcases x with ⟨b, x, y⟩
    change (∏ i : Fin (ts.length + 1),
      if (Fin.cons (α := fun _ => Bool) b (ts.selection y) i : Bool) then Fin.cons (α := fun _ => K) p ts.coefficients i else 1) = _
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact congrArg ((if b then p else 1) * ·) (ts.prod_selection y)

mutual
/-- Every node carries its own table, with parent coefficient in port zero. -/
def Tree.label : (t : Tree K) → (v : t.Vertex) → Signature K (t.arity v)
  | .node a b ts, .inl _ => table a (Fin.cons b ts.coefficients)
  | .node _ _ ts, .inr v => ts.label v
def Forest.label : (ts : Forest K) → (v : ts.Vertex) → Signature K (ts.arity v)
  | .nil, v => nomatch v
  | .cons _ t _, .inl v => t.label v
  | .cons _ _ ts, .inr v => ts.label v
end

mutual
/-- The zero-word coefficient of the original node at an address. -/
def Tree.zeroCoefficient : (t : Tree K) → t.Vertex → K
  | .node a _ _, .inl _ => a
  | .node _ _ ts, .inr v => ts.zeroCoefficient v
def Forest.zeroCoefficient : (ts : Forest K) → ts.Vertex → K
  | .nil, v => nomatch v
  | .cons _ t _, .inl v => t.zeroCoefficient v
  | .cons _ _ ts, .inr v => ts.zeroCoefficient v
end

mutual
/-- Ordered singleton coefficients, with parent at zero and children following. -/
def Tree.portCoefficient : (t : Tree K) → (v : t.Vertex) → Fin (t.arity v) → K
  | .node _ b ts, .inl _ => Fin.cons b ts.coefficients
  | .node _ _ ts, .inr v => ts.portCoefficient v
def Forest.portCoefficient : (ts : Forest K) → (v : ts.Vertex) → Fin (ts.arity v) → K
  | .nil, v => nomatch v
  | .cons _ t _, .inl v => t.portCoefficient v
  | .cons _ _ ts, .inr v => ts.portCoefficient v
end

mutual
theorem Tree.label_eq_table (t : Tree K) (v : t.Vertex) :
    t.label v = table (t.zeroCoefficient v) (t.portCoefficient v) := by
  cases t with
  | node a b ts =>
    cases v with
    | inl u => rfl
    | inr v => exact ts.label_eq_table v
theorem Forest.label_eq_table (ts : Forest K) (v : ts.Vertex) :
    ts.label v = table (ts.zeroCoefficient v) (ts.portCoefficient v) := by
  cases ts with
  | nil => exact Empty.elim v
  | cons p t ts =>
    cases v with
    | inl v => exact t.label_eq_table v
    | inr v => exact ts.label_eq_table v
end

@[simp] theorem Tree.label_zero (t : Tree K) (v : t.Vertex) :
    t.label v (fun _ => false) = t.zeroCoefficient v := by
  rw [t.label_eq_table, table_zero]

@[simp] theorem Tree.label_singleton (t : Tree K) (v : t.Vertex)
    (i : Fin (t.arity v)) :
    t.label v (fun j => decide (j = i)) = t.portCoefficient v i := by
  rw [t.label_eq_table, table_singleton]

omit [CommSemiring K] in
/-- The root parent port is an ordinary boundary occurrence, not a free stub. -/
@[simp] theorem Tree.portMap_root_zero (a b : K) (ts : Forest K) :
    (Tree.node a b ts).portMap ⟨.inl (), (0 : Fin (ts.length + 1))⟩ = .inl 0 := rfl

omit [CommSemiring K] in
/-- Child slots retain their order after the root's parent slot. -/
@[simp] theorem Tree.portMap_root_succ (a b : K) (ts : Forest K) (i : Fin ts.length) :
    (Tree.node a b ts).portMap ⟨.inl (), i.succ⟩ =
      .inr (ts.portMap (.inl i)) := rfl

omit [CommSemiring K] in
/-- Each child edge is oriented with its common-parent occurrence at true. -/
@[simp] theorem Forest.portMap_head_parent (p : K) (t : Tree K) (ts : Forest K) :
    (Forest.cons p t ts).portMap (.inl (0 : Fin (ts.length + 1))) =
      (.inl (), true) := rfl

omit [CommSemiring K] in
/-- Its child occurrence is the child's actual parent port, labeled false. -/
@[simp] theorem Forest.portMap_head_child (p : K) (t : Tree K) (ts : Forest K) :
    (Forest.cons p t ts).portMap
      (.inr ⟨.inl (t.portInv (.inl 0)).1, (t.portInv (.inl 0)).2⟩) =
      (.inl (), false) := by
  simp only [Forest.portMap, Sigma.eta, Tree.portMap_inv]

/-- The actual finite-index network. There is exactly one native X per edge. -/
def Tree.finiteNetwork (t : Tree K) : FiniteNetwork K t.Vertex t.Edge 1 where
  arity := t.arity
  ports := t.portEquiv
  vertex := t.label
  edge := fun _ => Signature.disequality

/-- Relabel node and edge addresses by `Fin` without changing ordered ports. -/
noncomputable def Tree.toNetwork (t : Tree K) : Network K 1 :=
  t.finiteNetwork.toNetwork

@[simp] theorem Tree.toNetwork_vertices (t : Tree K) :
    t.toNetwork.shape.vertices = t.vertices := t.card_vertex

@[simp] theorem Tree.toNetwork_edges (t : Tree K) :
    t.toNetwork.shape.edges = t.edges := t.card_edge

mutual
theorem Tree.label_oneHot (t : Tree K) (v : t.Vertex) :
    Signature.OneHot (t.label v) := by
  cases t with
  | node a b ts =>
    cases v with
    | inl u => exact table_oneHot a (Fin.cons b ts.coefficients)
    | inr v => exact ts.label_oneHot v
theorem Forest.label_oneHot (ts : Forest K) (v : ts.Vertex) :
    Signature.OneHot (ts.label v) := by
  cases ts with
  | nil => exact Empty.elim v
  | cons p t ts =>
    cases v with
    | inl v => exact t.label_oneHot v
    | inr v => exact ts.label_oneHot v
end

/-- Ordinary boundary and native endpoint assignment at a tree vertex. -/
def Tree.assignment (t : Tree K) (parent : Bool) (x : t.Choice)
    (v : t.Vertex) : Fin (t.arity v) → Bool := fun i =>
  Sum.elim (fun _ => parent)
    (FiniteNetwork.endpointChoiceAssignment (t.edgeChoices x)) (t.portMap ⟨v, i⟩)

/-- Assignment at a forest vertex, after its external child edge is included. -/
def Forest.assignment (ts : Forest K) (x : ts.Choice)
    (v : ts.Vertex) : Fin (ts.arity v) → Bool := fun i =>
  FiniteNetwork.endpointChoiceAssignment (ts.edgeChoices x) (ts.portMap (.inr ⟨v, i⟩))

omit [CommSemiring K] in
/-- Native assignments at the forest's common-parent ports follow child order. -/
theorem Forest.parent_assignment (ts : Forest K) (x : ts.Choice) (i : Fin ts.length) :
    FiniteNetwork.endpointChoiceAssignment (ts.edgeChoices x)
      (ts.portMap (.inl i)) = ts.selection x i := by
  cases ts with
  | nil => exact Fin.elim0 i
  | cons p t ts =>
    rcases x with ⟨b, x, y⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Forest.portMap, Fin.cases_succ, Forest.selection, Fin.cons_succ]
      change (if (ts.portMap (.inl j)).2 then
        ts.edgeChoices y (ts.portMap (.inl j)).1 else
        !(ts.edgeChoices y (ts.portMap (.inl j)).1)) = _
      exact ts.parent_assignment y j

omit [CommSemiring K] in
@[simp] theorem Tree.assignment_root (a b : K) (ts : Forest K)
    (parent : Bool) (x : ts.Choice) :
    (Tree.node a b ts).assignment parent x (.inl ()) =
      Fin.cons parent (ts.selection x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact ts.parent_assignment x j

omit [CommSemiring K] in
@[simp] theorem Tree.assignment_descendant (a b : K) (ts : Forest K)
    (parent : Bool) (x : ts.Choice) (v : ts.Vertex) :
    (Tree.node a b ts).assignment parent x (.inr v) = ts.assignment x v := rfl

omit [CommSemiring K] in
@[simp] theorem Forest.assignment_child (p : K) (t : Tree K) (ts : Forest K)
    (b : Bool) (x : t.Choice) (y : ts.Choice) (v : t.Vertex) :
    (Forest.cons p t ts).assignment (b, x, y) (.inl v) =
      t.assignment (!b) x v := by
  funext i
  unfold Forest.assignment Tree.assignment
  simp only [Forest.portMap]
  generalize h : t.portMap ⟨v, i⟩ = q
  cases q with
  | inl j => rfl
  | inr q =>
    rcases q with ⟨e, side⟩
    cases side <;> rfl

omit [CommSemiring K] in
@[simp] theorem Forest.assignment_rest (p : K) (t : Tree K) (ts : Forest K)
    (b : Bool) (x : t.Choice) (y : ts.Choice) (v : ts.Vertex) :
    (Forest.cons p t ts).assignment (b, x, y) (.inr v) =
      ts.assignment y v := by
  funext i
  unfold Forest.assignment
  simp only [Forest.portMap]
  generalize h : ts.portMap (.inr ⟨v, i⟩) = q
  rcases q with ⟨e, side⟩
  cases side <;> rfl

mutual
/-- The genuine product of graph-vertex tables equals the recursive term. -/
theorem Tree.prod_label_assignment (t : Tree K) (parent : Bool) (x : t.Choice) :
    (∏ v, t.label v (t.assignment parent x v)) = t.weight parent x := by
  classical
  cases t with
  | node a b ts =>
    change (∏ v : Unit ⊕ ts.Vertex, _) = _
    rw [Fintype.prod_sum_type]
    rw [Fintype.prod_unique]
    change table a (Fin.cons b ts.coefficients)
        ((Tree.node a b ts).assignment parent x (.inl ())) *
        (∏ v, ts.label v (ts.assignment x v)) = _
    rw [Tree.assignment_root, table_cons, Forest.weight_selection,
      Forest.prod_selection, ts.prod_label_assignment]
    unfold Tree.weight
    split <;> simp_all
/-- Each child edge gives the child its opposite endpoint bit. -/
theorem Forest.prod_label_assignment (ts : Forest K) (x : ts.Choice) :
    (∏ v, ts.label v (ts.assignment x v)) = ts.weight x := by
  classical
  cases ts with
  | nil => simp [Forest.Vertex, Forest.weight]
  | cons p t ts =>
    rcases x with ⟨b, x, y⟩
    change (∏ v : t.Vertex ⊕ ts.Vertex, _) = _
    rw [Fintype.prod_sum_type]
    simp only [Forest.label, Forest.assignment_child, Forest.assignment_rest,
      Tree.prod_label_assignment, Forest.prod_label_assignment, Forest.weight]
end

/-- The finite-index graph sum is the evaluator's independent endpoint sum. -/
theorem Tree.denote_finiteNetwork (t : Tree K) (parent : Bool) :
    t.finiteNetwork.denote (fun _ => parent) = t.denote parent := by
  classical
  change (FiniteNetwork.mk t.arity t.portEquiv t.label
    (fun _ => Signature.disequality)).denote _ = _
  rw [FiniteNetwork.denote_disequality_apply]
  unfold Tree.denote
  rw [← t.choiceEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  exact t.prod_label_assignment parent x

/-- Actual `Network.denote`, preserving the exact boundary and every scalar. -/
theorem Tree.denote_toNetwork (t : Tree K) (parent : Bool) :
    t.toNetwork.denote (fun _ => parent) = t.denote parent := by
  rw [Tree.toNetwork, FiniteNetwork.denote_toNetwork]
  exact t.denote_finiteNetwork parent

/-- The theorem also applies to every ordinary boundary word directly. -/
theorem Tree.denote_toNetwork_apply (t : Tree K) (x : Fin 1 → Bool) :
    t.toNetwork.denote x = t.denote (x 0) := by
  have hx : x = fun _ => x 0 := funext fun i => congrArg x (Subsingleton.elim i 0)
  rw [hx]
  exact t.denote_toNetwork (x 0)

/-- Every edge retains the native disequality tensor exactly. -/
@[simp] theorem Tree.toNetwork_edge (t : Tree K) (e : Fin t.toNetwork.shape.edges) :
    t.toNetwork.edge e = Signature.disequality := rfl

/-- The two evaluator outputs are the actual graph's two boundary values. -/
theorem Tree.eval_network_correct (t : Tree K) :
    t.eval = (t.toNetwork.denote (fun _ => false),
      t.toNetwork.denote (fun _ => true)) := by
  simp only [Tree.denote_toNetwork, Tree.eval_correct]

/-- Arithmetic program correctness for the actual graph, with its graph counts.
This is an arithmetic-instruction count, not a polynomial bit-time claim. -/
theorem Tree.program_network_spec (t : Tree K) :
    t.program.run =
      ((t.toNetwork.denote (fun _ => false), t.toNetwork.denote (fun _ => true)),
        3 * t.toNetwork.shape.vertices + 5 * t.toNetwork.shape.edges) := by
  simp only [Tree.denote_toNetwork, Tree.toNetwork_vertices, Tree.toNetwork_edges,
    Tree.program_spec]

/-- Every relabeled network vertex has actual one-hot support. -/
theorem Tree.toNetwork_oneHot (t : Tree K) (v : Fin t.toNetwork.shape.vertices) :
    Signature.OneHot (t.toNetwork.vertex v) :=
  t.label_oneHot ((Fintype.equivFin t.Vertex).symm v)

/-- The constructed graph has the exact tree count. -/
theorem Tree.toNetwork_edges_add_one (t : Tree K) :
    t.toNetwork.shape.edges + 1 = t.toNetwork.shape.vertices := by
  simpa only [Tree.toNetwork_edges, Tree.toNetwork_vertices] using t.edges_add_one_eq_vertices

/-- Linear arithmetic count measured in the constructed graph itself. -/
theorem Tree.program_network_operations_le (t : Tree K) :
    t.program.run.2 ≤ 5 * (t.toNetwork.shape.vertices + t.toNetwork.shape.edges) := by
  simpa only [Tree.toNetwork_vertices, Tree.toNetwork_edges] using t.program_operations_le

end Holant.OneHot
