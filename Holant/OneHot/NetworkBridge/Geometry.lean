import Holant.OneHot.NetworkBridge

/-! The recursive tree geometry agrees with every actual oriented endpoint. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot
variable {K : Type*}

/-- The actual root node address, independent of its coefficients. -/
def Tree.rootVertex : (t : Tree K) → t.Vertex
  | .node _ _ _ => .inl ()

mutual
/-- The root plus every edge's child enumerates each tree vertex exactly once. -/
def Tree.edgeRootEquiv : (t : Tree K) → (Unit ⊕ t.Edge) ≃ t.Vertex
  | .node _ _ ts => Equiv.sumCongr (Equiv.refl Unit) ts.edgeVertexEquiv
/-- Every forest edge includes its incoming parent edge, so its child vertices
are precisely all original forest vertices. -/
def Forest.edgeVertexEquiv : (ts : Forest K) → ts.Edge ≃ ts.Vertex
  | .nil => Equiv.refl Empty
  | .cons _ t ts => (Equiv.sumAssoc Unit t.Edge ts.Edge).symm.trans
      (Equiv.sumCongr t.edgeRootEquiv ts.edgeVertexEquiv)
end

@[simp] theorem Tree.edgeRootEquiv_root (t : Tree K) :
    t.edgeRootEquiv (.inl ()) = t.rootVertex := by cases t; rfl

/-- The edge's false endpoint is its child, never the root. -/
def Tree.edgeNonrootEquiv : (t : Tree K) → t.Edge ≃ {v : t.Vertex // v ≠ t.rootVertex}
  | .node a b ts => {
    toFun := fun e => ⟨.inr (ts.edgeVertexEquiv e), by intro h; cases h⟩
    invFun := fun v => by
      rcases v with ⟨v, hv⟩
      cases v with
      | inl u => exact False.elim (hv (by cases u; rfl))
      | inr w => exact ts.edgeVertexEquiv.symm w
    left_inv := fun e => ts.edgeVertexEquiv.symm_apply_apply e
    right_inv := by
      rintro ⟨v, hv⟩
      cases v with
      | inl u => cases u; exact (hv rfl).elim
      | inr v => apply Subtype.ext; exact congrArg Sum.inr (ts.edgeVertexEquiv.apply_symm_apply v) }

mutual
theorem Tree.arity_pos (t : Tree K) (v : t.Vertex) : 0 < t.arity v := by
  cases t with
  | node a b ts =>
    cases v with
    | inl _ => exact Nat.succ_pos _
    | inr v => exact ts.arity_pos v
theorem Forest.arity_pos (ts : Forest K) (v : ts.Vertex) : 0 < ts.arity v := by
  cases ts with
  | nil => exact Empty.elim v
  | cons c t ts =>
    cases v with
    | inl v => exact t.arity_pos v
    | inr v => exact ts.arity_pos v
end

def Tree.parentOccurrence (t : Tree K) (v : t.Vertex) : t.Occurrence :=
  ⟨v, ⟨0, t.arity_pos v⟩⟩
def Forest.parentOccurrence (ts : Forest K) (v : ts.Vertex) : ts.Occurrence :=
  ⟨v, ⟨0, ts.arity_pos v⟩⟩

mutual
/-- Every actual false endpoint is the selected child's literal parent port 0. -/
theorem Tree.portInv_false (t : Tree K) (e : t.Edge) :
    t.portInv (.inr (e, false)) = t.parentOccurrence (t.edgeRootEquiv (.inr e)) := by
  cases t with
  | node a b ts =>
    simp only [Tree.portInv, Forest.portInv_false]
    rfl
theorem Forest.portInv_false (ts : Forest K) (e : ts.Edge) :
    ts.portInv (e, false) = .inr (ts.parentOccurrence (ts.edgeVertexEquiv e)) := by
  cases ts with
  | nil => exact Empty.elim e
  | cons c t ts =>
    rcases e with u | (e | e)
    · cases u
      cases t
      rfl
    · simp only [Forest.portInv]
      rw [t.portInv_false]
      rfl
    · simp only [Forest.portInv, Forest.portInv_false]
      rfl
end

theorem Tree.false_endpoint_eq (t : Tree K) (e : t.Edge) :
    (t.portInv (.inr (e, false))).1 = (t.edgeNonrootEquiv e).1 := by
  rw [t.portInv_false]
  cases t
  rfl

mutual
/-- Structural parent address; only the tree root has no parent. -/
def Tree.parentVertex : (t : Tree K) → t.Vertex → Option t.Vertex
  | .node _ _ _, .inl _ => none
  | .node _ _ ts, .inr v =>
      some ((ts.parentVertex v).elim (.inl ()) Sum.inr)
/-- Forest roots have their common external parent, represented by `none`. -/
def Forest.parentVertex : (ts : Forest K) → ts.Vertex → Option ts.Vertex
  | .nil, v => nomatch v
  | .cons _ t _, .inl v => (t.parentVertex v).map Sum.inl
  | .cons _ _ ts, .inr v => (ts.parentVertex v).map Sum.inr
end

@[simp] theorem Tree.parentVertex_root (t : Tree K) :
    t.parentVertex t.rootVertex = none := by cases t; rfl

mutual
/-- The actual true endpoint is exactly the structural parent of its child. -/
theorem Tree.parentVertex_edge (t : Tree K) (e : t.Edge) :
    t.parentVertex (t.edgeRootEquiv (.inr e)) =
      some (t.portInv (.inr (e, true))).1 := by
  cases t with
  | node a b ts =>
    change some ((ts.parentVertex (ts.edgeVertexEquiv e)).elim (.inl ()) Sum.inr) = _
    rw [ts.parentVertex_edge]
    cases h : ts.portInv (e, true) <;> simp [Tree.portInv, h]
theorem Forest.parentVertex_edge (ts : Forest K) (e : ts.Edge) :
    ts.parentVertex (ts.edgeVertexEquiv e) =
      match ts.portInv (e, true) with
      | .inl _ => none
      | .inr p => some p.1 := by
  cases ts with
  | nil => exact Empty.elim e
  | cons c t ts =>
    rcases e with u | (e | e)
    · cases u
      change (t.parentVertex (t.edgeRootEquiv (.inl ()))).map Sum.inl = none
      rw [t.edgeRootEquiv_root, t.parentVertex_root]
      rfl
    · change (t.parentVertex (t.edgeRootEquiv (.inr e))).map Sum.inl = _
      rw [t.parentVertex_edge]
      rfl
    · change (ts.parentVertex (ts.edgeVertexEquiv e)).map Sum.inr = _
      rw [ts.parentVertex_edge]
      cases h : ts.portInv (e, true) <;> simp [Forest.portInv, h]
end

theorem Tree.parentVertex_nonroot (t : Tree K) (e : t.Edge) :
    t.parentVertex (t.edgeNonrootEquiv e).1 =
      some (t.portInv (.inr (e, true))).1 := by
  have h := t.parentVertex_edge e
  cases t
  exact h

end Holant.OneHot
