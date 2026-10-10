import Holant.OneHot.Decomposition.Descendants

open scoped Classical
set_option backward.isDefEq.respectTransparency false
/-!
# Original ordered ports of an extracted tree

With no surplus original edges, the actual ports at a vertex are exactly its
own parent occurrence, when it has one, and the opposite parent occurrence of
each genuine child. The bijections below are proved from original edge identity
and the original closed port equivalence; no incidence equivalence is assumed.
-/

namespace Holant.OneHot.Decomposition.RootedSpanning

variable {V E : Type*} {endpoint : E → Bool → V} {root : V}
variable (t : RootedSpanning endpoint root)

/-- Use one fixed finite enumeration of genuine children across specializations. -/
noncomputable instance childFintype [Fintype V] (v : V) : Fintype (t.Child v) := by
  classical
  unfold Child
  infer_instance

/-- The own-parent incidence exists exactly when this vertex is not the root. -/
abbrev OwnParent (_t : RootedSpanning endpoint root) (v : V) := {u : {u : V // u ≠ root} // u.1 = v}

/-- A vertex has an own-parent occurrence exactly when it is not the root. -/
theorem ownParent_nonempty_iff (v : V) : Nonempty (t.OwnParent v) ↔ v ≠ root := by
  constructor
  · rintro ⟨u⟩
    exact u.2 ▸ u.1.2
  · intro h
    exact ⟨⟨⟨v, h⟩, rfl⟩⟩

/-- The exact incidences at one vertex of the extracted tree. -/
abbrev LocalTreePort (v : V) := t.OwnParent v ⊕ t.Child v

/-- The literal original oriented edge end belonging to a local tree port. -/
def localEnd (v : V) : t.LocalTreePort v → E × Bool
  | .inl u => t.parentEnd u.1
  | .inr u => ((t.parentEnd ⟨u.1, u.2.1⟩).1, !(t.parentEnd ⟨u.1, u.2.1⟩).2)

@[simp] theorem localEnd_inl (v : V) (u : t.OwnParent v) :
    t.localEnd v (.inl u) = t.parentEnd u.1 := rfl

@[simp] theorem localEnd_inr (v : V) (u : t.Child v) :
    t.localEnd v (.inr u) =
      ((t.parentEnd ⟨u.1, u.2.1⟩).1, !(t.parentEnd ⟨u.1, u.2.1⟩).2) := rfl

/-- Both kinds of extracted incidence are at the named original vertex. -/
theorem localEnd_endpoint (v : V) (p : t.LocalTreePort v) :
    endpoint (t.localEnd v p).1 (t.localEnd v p).2 = v := by
  cases p with
  | inl u => exact (t.child_endpoint u.1).trans u.2
  | inr u =>
    simpa only [localEnd, parent, dite_eq_right u.2.1] using u.2.2

/-- Parent-edge injectivity and the two distinct orientations prevent any
original edge-end occurrence from being duplicated. -/
theorem localEnd_injective (v : V) : Function.Injective (t.localEnd v) := by
  rintro (u | u) (w | w) h
  · have he : u.1 = w.1 := t.parentEdge_injective (by
      simpa only [localEnd, parentEdge] using congrArg (fun q : E × Bool => q.1) h)
    exact congrArg Sum.inl (Subtype.ext he)
  · have he : u.1 = ⟨w.1, w.2.1⟩ := t.parentEdge_injective (by
      simpa only [localEnd, parentEdge] using congrArg (fun q : E × Bool => q.1) h)
    have hb := congrArg (fun q : E × Bool => q.2) h
    change (t.parentEnd u.1).2 = !(t.parentEnd ⟨w.1, w.2.1⟩).2 at hb
    rw [he] at hb
    cases hbit : (t.parentEnd ⟨w.1, w.2.1⟩).2 <;> simp only [hbit, Bool.not_false, Bool.not_true] at hb <;> contradiction
  · have he : (⟨u.1, u.2.1⟩ : {v : V // v ≠ root}) = w.1 :=
      t.parentEdge_injective (by
      simpa only [localEnd, parentEdge] using congrArg (fun q : E × Bool => q.1) h)
    have hb := congrArg (fun q : E × Bool => q.2) h
    change (!(t.parentEnd ⟨u.1, u.2.1⟩).2) = (t.parentEnd w.1).2 at hb
    rw [he] at hb
    cases hbit : (t.parentEnd w.1).2 <;> simp only [hbit, Bool.not_false, Bool.not_true] at hb <;> contradiction
  · have he : (⟨u.1, u.2.1⟩ : {v : V // v ≠ root}) = ⟨w.1, w.2.1⟩ :=
      t.parentEdge_injective (by
      simpa only [localEnd, parentEdge] using congrArg (fun q : E × Bool => q.1) h)
    exact congrArg Sum.inr (Subtype.ext (congrArg (fun q : {v : V // v ≠ root} => q.1) he))

/-- Every original end at this vertex is its own parent or a child's parent end. -/
theorem localEnd_surjective (h : Function.Surjective t.parentEdge) (v : V)
    (q : E × Bool) (hq : endpoint q.1 q.2 = v) :
    ∃ p : t.LocalTreePort v, t.localEnd v p = q := by
  obtain ⟨u, hu⟩ := h q.1
  by_cases hb : q.2 = (t.parentEnd u).2
  · have huv : u.1 = v := by
      rw [← t.child_endpoint u, show (t.parentEnd u).1 = q.1 from hu, ← hb]
      exact hq
    exact ⟨.inl ⟨u, huv⟩, Prod.ext hu hb.symm⟩
  · have hb' : (!(t.parentEnd u).2) = q.2 := by
      cases h₁ : (t.parentEnd u).2 <;> cases h₂ : q.2 <;> simp_all
    have huv : t.parent u.1 = v := by
      rw [parent, dite_eq_right u.2]
      change endpoint (t.parentEnd u).1 (!(t.parentEnd u).2) = v
      rw [show (t.parentEnd u).1 = q.1 from hu, hb']
      exact hq
    exact ⟨.inr ⟨u.1, u.2, huv⟩, Prod.ext hu hb'⟩

/-- A proved bijection with the fiber of the original endpoint function. -/
noncomputable def localEndEquiv (h : Function.Surjective t.parentEdge) (v : V) :
    t.LocalTreePort v ≃ {q : E × Bool // endpoint q.1 q.2 = v} :=
  Equiv.ofBijective (fun p => ⟨t.localEnd v p, t.localEnd_endpoint v p⟩)
    ⟨fun _ _ hp => t.localEnd_injective v (congrArg Subtype.val hp), by
      rintro ⟨q, hq⟩
      obtain ⟨p, hp⟩ := t.localEnd_surjective h v q hq
      exact ⟨p, Subtype.ext hp⟩⟩

@[simp] theorem localEndEquiv_val (h : Function.Surjective t.parentEdge) (v : V)
    (p : t.LocalTreePort v) : (t.localEndEquiv h v p).1 = t.localEnd v p := rfl

/-- An empty surplus is exactly the coverage hypothesis needed here. -/
theorem parentEdge_surjective_of_isEmpty_surplus [IsEmpty t.Surplus] :
    Function.Surjective t.parentEdge := by
  intro e
  by_contra h
  exact (inferInstance : IsEmpty t.Surplus).false ⟨e, h⟩

/-- No-surplus and coverage of all literal original edges are equivalent. -/
theorem parentEdge_surjective_iff_isEmpty_surplus :
    Function.Surjective t.parentEdge ↔ IsEmpty t.Surplus := by
  constructor
  · intro h
    exact ⟨fun e => e.2 (h e.1)⟩
  · intro h
    let := h
    exact t.parentEdge_surjective_of_isEmpty_surplus

/-- The tree edge count supplies the coverage hypothesis without an extra
incidence assumption. -/
theorem parentEdge_surjective_of_tree_count [Fintype V] [Fintype E]
    (h : Fintype.card E + 1 = Fintype.card V) : Function.Surjective t.parentEdge := by
  have hz := t.surplus_card_eq_zero h
  let : IsEmpty t.Surplus := Fintype.card_eq_zero_iff.mp hz
  exact t.parentEdge_surjective_of_isEmpty_surplus

end Holant.OneHot.Decomposition.RootedSpanning

namespace Holant.NetworkShape

/-- A local ordered port is the fiber of the vertex projection on occurrences. -/
def localOccurrenceEquiv (s : NetworkShape 0) (v : Fin s.vertices) :
    Fin (s.arity v) ≃ {p : Σ w : Fin s.vertices, Fin (s.arity w) // p.1 = v} where
  toFun i := ⟨⟨v, i⟩, rfl⟩
  invFun p := p.2 ▸ p.1.2
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨w, i⟩, h⟩; cases h; rfl

/-- Restrict the literal original port bijection to one vertex, without changing
any local port number, edge identity, or endpoint orientation. -/
def localEndFiberEquiv (s : NetworkShape 0) (v : Fin s.vertices) :
    Fin (s.arity v) ≃ {q : Fin s.edges × Bool // s.endpoint q.1 q.2 = v} :=
  (s.localOccurrenceEquiv v).trans (s.closedPorts.subtypeEquiv (fun p => by
    simp only [endpoint, Prod.eta, Equiv.symm_apply_apply]))

@[simp] theorem localEndFiberEquiv_val (s : NetworkShape 0) (v : Fin s.vertices)
    (i : Fin (s.arity v)) : (s.localEndFiberEquiv v i).1 = s.closedPorts ⟨v, i⟩ := rfl

end Holant.NetworkShape

namespace Holant.OneHot.Decomposition.RootedSpanning

variable {s : NetworkShape 0} {root : Fin s.vertices}
variable (t : RootedSpanning s.endpoint root)

/-- Every actual original ordered port appears exactly once, as an own-parent
incidence or the opposite end of a child's parent edge. -/
noncomputable def originalPortEquiv (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) : Fin (s.arity v) ≃ t.LocalTreePort v :=
  (s.localEndFiberEquiv v).trans (t.localEndEquiv h v).symm

/-- The bijection retains the complete original oriented edge identity. -/
theorem localEnd_originalPortEquiv (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (i : Fin (s.arity v)) :
    t.localEnd v (t.originalPortEquiv h v i) = s.closedPorts ⟨v, i⟩ := by
  change (t.localEndEquiv h v ((t.localEndEquiv h v).symm
    (s.localEndFiberEquiv v i))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The inverse uses the literal original `closedPorts.symm`, so no local order
or endpoint orientation is silently replaced. -/
theorem originalPortEquiv_symm_occurrence (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (p : t.LocalTreePort v) :
    (⟨v, (t.originalPortEquiv h v).symm p⟩ : Σ w, Fin (s.arity w)) =
      s.closedPorts.symm (t.localEnd v p) := by
  apply s.closedPorts.injective
  rw [Equiv.apply_symm_apply]
  have hi := t.localEnd_originalPortEquiv h v ((t.originalPortEquiv h v).symm p)
  rw [Equiv.apply_symm_apply] at hi
  exact hi.symm

@[simp] theorem originalPortEquiv_symm_parent (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (u : t.OwnParent v) :
    (⟨v, (t.originalPortEquiv h v).symm (.inl u)⟩ : Σ w, Fin (s.arity w)) =
      s.closedPorts.symm (t.parentEnd u.1) :=
  t.originalPortEquiv_symm_occurrence h v (.inl u)

@[simp] theorem originalPortEquiv_symm_child (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (u : t.Child v) :
    (⟨v, (t.originalPortEquiv h v).symm (.inr u)⟩ : Σ w, Fin (s.arity w)) =
      s.closedPorts.symm
        ((t.parentEnd ⟨u.1, u.2.1⟩).1, !(t.parentEnd ⟨u.1, u.2.1⟩).2) :=
  t.originalPortEquiv_symm_occurrence h v (.inr u)

end Holant.OneHot.Decomposition.RootedSpanning

namespace Holant.OneHot.Decomposition.RootedSpanning

variable {V E : Type*} {endpoint : E → Bool → V} {root : V}
variable (t : RootedSpanning endpoint root)

/-- The actual root has only child incidences, with no extra parent stub. -/
def rootLocalTreePortEquiv : t.LocalTreePort root ≃ t.Child root where
  toFun
    | .inl u => (u.1.2 u.2).elim
    | .inr u => u
  invFun := Sum.inr
  left_inv := by rintro (u | u); exact (u.1.2 u.2).elim; rfl
  right_inv _ := rfl

@[simp] theorem rootLocalTreePortEquiv_symm (u : t.Child root) :
    t.rootLocalTreePortEquiv.symm u = .inr u := rfl

/-- A non-root has exactly one own-parent incidence. -/
def ownParentEquiv (v : V) (hv : v ≠ root) : t.OwnParent v ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨⟨v, hv⟩, rfl⟩
  left_inv u := by apply Subtype.ext; apply Subtype.ext; exact u.2.symm
  right_inv u := by cases u; rfl

/-- The non-root port slots are one parent followed by genuine children. -/
def nonrootLocalTreePortEquiv (v : V) (hv : v ≠ root) :
    t.LocalTreePort v ≃ Unit ⊕ t.Child v :=
  Equiv.sumCongr (t.ownParentEquiv v hv) (Equiv.refl _)

@[simp] theorem nonrootLocalTreePortEquiv_symm_parent (v : V) (hv : v ≠ root) :
    (t.nonrootLocalTreePortEquiv v hv).symm (.inl ()) = .inl ⟨⟨v, hv⟩, rfl⟩ := rfl

@[simp] theorem nonrootLocalTreePortEquiv_symm_child (v : V) (hv : v ≠ root)
    (u : t.Child v) :
    (t.nonrootLocalTreePortEquiv v hv).symm (.inr u) = .inr u := rfl

/-- Enumerate a single parent at zero and children in the same `equivFin` order
used by recursive tree unfolding. -/
noncomputable def parentChildSlotsEquiv [Fintype V] (v : V) :
    (Unit ⊕ t.Child v) ≃ Fin (Fintype.card (t.Child v) + 1) := by
  classical
  exact {
    toFun := fun p => match p with
      | .inl _ => 0
      | .inr u => (Fintype.equivFin (t.Child v) u).succ
    invFun := Fin.cases (.inl ()) (fun i => .inr ((Fintype.equivFin (t.Child v)).symm i))
    left_inv := by rintro (u | u); cases u; rfl; simp
    right_inv := by intro i; cases i using Fin.cases <;> simp }

@[simp] theorem parentChildSlotsEquiv_symm_zero [Fintype V] (v : V) :
    (t.parentChildSlotsEquiv v).symm 0 = .inl () := rfl

@[simp] theorem parentChildSlotsEquiv_symm_succ [Fintype V] (v : V)
    (i : Fin (Fintype.card (t.Child v))) :
    (t.parentChildSlotsEquiv v).symm i.succ =
      .inr ((Fintype.equivFin (t.Child v)).symm i) := rfl

end Holant.OneHot.Decomposition.RootedSpanning

namespace Holant.OneHot.Decomposition.RootedSpanning

variable {s : NetworkShape 0} {root : Fin s.vertices}
variable (t : RootedSpanning s.endpoint root)

/-- Exact original root ports, with the nonexistent own-parent slot removed. -/
noncomputable def rootOriginalPortEquiv (h : Function.Surjective t.parentEdge) :
    Fin (s.arity root) ≃ t.Child root :=
  (t.originalPortEquiv h root).trans t.rootLocalTreePortEquiv

/-- Exact original non-root ports, with the unique parent explicitly first. -/
noncomputable def nonrootOriginalPortEquiv (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (hv : v ≠ root) : Fin (s.arity v) ≃ Unit ⊕ t.Child v :=
  (t.originalPortEquiv h v).trans (t.nonrootLocalTreePortEquiv v hv)

/-- The root's ordered child list is related to the arbitrary original order. -/
noncomputable def rootOrderedPortEquiv (h : Function.Surjective t.parentEdge) :
    Fin (s.arity root) ≃ Fin (Fintype.card (t.Child root)) := by
  classical
  exact (t.rootOriginalPortEquiv h).trans (Fintype.equivFin (t.Child root))

/-- Parent zero and then the exact same child order used by tree unfolding. -/
noncomputable def nonrootOrderedPortEquiv (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (hv : v ≠ root) :
    Fin (s.arity v) ≃ Fin (Fintype.card (t.Child v) + 1) :=
  (t.nonrootOriginalPortEquiv h v hv).trans (t.parentChildSlotsEquiv v)

/-- The actual root's degree is its number of genuine children. -/
theorem root_arity_eq_children (h : Function.Surjective t.parentEdge) :
    s.arity root = Fintype.card (t.Child root) := by
  classical
  simpa only [Fintype.card_fin] using Fintype.card_congr (t.rootOriginalPortEquiv h)

/-- Every proper descendant has one parent and exactly its genuine child ports. -/
theorem nonroot_arity_eq_children_add_one (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (hv : v ≠ root) :
    s.arity v = Fintype.card (t.Child v) + 1 := by
  classical
  simpa only [Fintype.card_fin] using Fintype.card_congr (t.nonrootOrderedPortEquiv h v hv)

@[simp] theorem rootOriginalPortEquiv_symm_occurrence (h : Function.Surjective t.parentEdge)
    (u : t.Child root) :
    (⟨root, (t.rootOriginalPortEquiv h).symm u⟩ : Σ w, Fin (s.arity w)) =
      s.closedPorts.symm
        ((t.parentEnd ⟨u.1, u.2.1⟩).1, !(t.parentEnd ⟨u.1, u.2.1⟩).2) :=
  t.originalPortEquiv_symm_child h root u

@[simp] theorem nonrootOriginalPortEquiv_symm_parent (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (hv : v ≠ root) :
    (⟨v, (t.nonrootOriginalPortEquiv h v hv).symm (.inl ())⟩ : Σ w, Fin (s.arity w)) =
      s.closedPorts.symm (t.parentEnd ⟨v, hv⟩) :=
  t.originalPortEquiv_symm_parent h v ⟨⟨v, hv⟩, rfl⟩

@[simp] theorem nonrootOriginalPortEquiv_symm_child (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (hv : v ≠ root) (u : t.Child v) :
    (⟨v, (t.nonrootOriginalPortEquiv h v hv).symm (.inr u)⟩ : Σ w, Fin (s.arity w)) =
      s.closedPorts.symm
        ((t.parentEnd ⟨u.1, u.2.1⟩).1, !(t.parentEnd ⟨u.1, u.2.1⟩).2) :=
  t.originalPortEquiv_symm_child h v u

@[simp] theorem nonrootOrderedPortEquiv_symm_zero (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (hv : v ≠ root) :
    (⟨v, (t.nonrootOrderedPortEquiv h v hv).symm 0⟩ : Σ w, Fin (s.arity w)) =
      s.closedPorts.symm (t.parentEnd ⟨v, hv⟩) :=
  t.nonrootOriginalPortEquiv_symm_parent h v hv

@[simp] theorem nonrootOrderedPortEquiv_symm_succ (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (hv : v ≠ root) (i : Fin (Fintype.card (t.Child v))) :
    (⟨v, (t.nonrootOrderedPortEquiv h v hv).symm i.succ⟩ : Σ w, Fin (s.arity w)) =
      let u := (Fintype.equivFin (t.Child v)).symm i
      s.closedPorts.symm
        ((t.parentEnd ⟨u.1, u.2.1⟩).1, !(t.parentEnd ⟨u.1, u.2.1⟩).2) :=
  t.nonrootOriginalPortEquiv_symm_child h v hv _

@[simp] theorem rootOrderedPortEquiv_symm_occurrence (h : Function.Surjective t.parentEdge)
    (i : Fin (Fintype.card (t.Child root))) :
    (⟨root, (t.rootOrderedPortEquiv h).symm i⟩ : Σ w, Fin (s.arity w)) =
      let u := (Fintype.equivFin (t.Child root)).symm i
      s.closedPorts.symm
        ((t.parentEnd ⟨u.1, u.2.1⟩).1, !(t.parentEnd ⟨u.1, u.2.1⟩).2) :=
  t.rootOriginalPortEquiv_symm_occurrence h _

/-- Any original ordered coefficient table transports to parent-first order by
literal lookup, with no symmetry or nonzero assumption on the coefficients. -/
theorem nonrootOrderedPortEquiv_coefficient {K : Type*}
    (c : (Σ w, Fin (s.arity w)) → K) (h : Function.Surjective t.parentEdge)
    (v : Fin s.vertices) (hv : v ≠ root) (i : Fin (Fintype.card (t.Child v) + 1)) :
    c ⟨v, (t.nonrootOrderedPortEquiv h v hv).symm i⟩ =
      Fin.cons (α := fun _ => K) (c (s.closedPorts.symm (t.parentEnd ⟨v, hv⟩)))
        (fun j => let u := (Fintype.equivFin (t.Child v)).symm j
          c (s.closedPorts.symm
            ((t.parentEnd ⟨u.1, u.2.1⟩).1, !(t.parentEnd ⟨u.1, u.2.1⟩).2))) i := by
  cases i using Fin.cases with
  | zero => exact congrArg c (t.nonrootOrderedPortEquiv_symm_zero h v hv)
  | succ i => exact congrArg c (t.nonrootOrderedPortEquiv_symm_succ h v hv i)

/-- Coefficient transport is the literal original occurrence table, including
arbitrary asymmetric and zero coefficients. -/
theorem originalPortEquiv_coefficient {K : Type*} (c : (Σ w, Fin (s.arity w)) → K)
    (h : Function.Surjective t.parentEdge) (v : Fin s.vertices) (p : t.LocalTreePort v) :
    c ⟨v, (t.originalPortEquiv h v).symm p⟩ =
      c (s.closedPorts.symm (t.localEnd v p)) :=
  congrArg c (t.originalPortEquiv_symm_occurrence h v p)

end Holant.OneHot.Decomposition.RootedSpanning
