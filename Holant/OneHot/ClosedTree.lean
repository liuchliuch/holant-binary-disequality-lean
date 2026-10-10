import Holant.OneHot.NetworkBridge

/-!
# Actual closed rooted trees

The root has only its child ports: its virtual parent port is removed, rather
than pinned by an extra supplied signature. Every non-root vertex retains its
ordered parent/child ports. The resulting closed Network is evaluated by a
literal division-free arithmetic program. This does not extract trees from
arbitrary graph components or establish machine bit complexity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot

variable {K : Type*}

/-- Edge choices of the forest include each edge from its common root. -/
def Forest.choiceEquiv (ts : Forest K) : ts.Choice ≃ (ts.Edge → Bool) where
  toFun := ts.edgeChoices
  invFun := ts.fromEdgeChoices
  left_inv := ts.fromEdgeChoices_edgeChoices
  right_inv := ts.edgeChoices_fromEdgeChoices

/-- A genuine root vertex, followed by all original descendant vertices. -/
abbrev Forest.ClosedVertex (ts : Forest K) := Unit ⊕ ts.Vertex

/-- The root has no virtual parent port. -/
def Forest.closedArity (ts : Forest K) : ts.ClosedVertex → ℕ
  | .inl _ => ts.length
  | .inr v => ts.arity v

/-- Rearrange actual port occurrences into the forest's root/descendant slots. -/
def Forest.closedSlots (ts : Forest K) :
    (Σ v : ts.ClosedVertex, Fin (ts.closedArity v)) ≃ (Fin ts.length ⊕ ts.Occurrence) where
  toFun := fun p => match p with
    | ⟨.inl _, i⟩ => .inl i
    | ⟨.inr v, i⟩ => .inr ⟨v, i⟩
  invFun := fun p => match p with
    | .inl i => ⟨.inl (), i⟩
    | .inr ⟨v, i⟩ => ⟨.inr v, i⟩
  left_inv := by
    rintro ⟨v, i⟩
    cases v with
    | inl u => cases u; rfl
    | inr v => rfl
  right_inv := by
    intro p
    cases p <;> rfl

/-- The root and descendant slots biject with the two ends of every child edge. -/
def Forest.closedPortEquiv (ts : Forest K) :
    (Σ v : ts.ClosedVertex, Fin (ts.closedArity v)) ≃ (Fin 0 ⊕ (ts.Edge × Bool)) where
  toFun p := .inr (ts.portMap (ts.closedSlots p))
  invFun p := Sum.elim Fin.elim0 (fun q => ts.closedSlots.symm (ts.portInv q)) p
  left_inv p := by simp only [Sum.elim_inr, Forest.portInv_map, Equiv.symm_apply_apply]
  right_inv p := by
    cases p with
    | inl i => exact Fin.elim0 i
    | inr q => simp only [Sum.elim_inr, Equiv.apply_symm_apply, Forest.portMap_inv]

variable [CommSemiring K]

/-- Keep the original child singleton coefficients and root zero-word value. -/
def Forest.closedLabel (ts : Forest K) (a : K) :
    (v : ts.ClosedVertex) → Signature K (ts.closedArity v)
  | .inl _ => table a ts.coefficients
  | .inr v => ts.label v

/-- Actual finite-index closed tree, without added pins or boundary stubs. -/
def Forest.closedFiniteNetwork (ts : Forest K) (a : K) :
    FiniteNetwork K ts.ClosedVertex ts.Edge 0 where
  arity := ts.closedArity
  ports := ts.closedPortEquiv
  vertex := ts.closedLabel a
  edge := fun _ => Signature.disequality

/-- Relabel the closed tree by finite natural indices without changing its ports. -/
noncomputable def Forest.closedNetwork (ts : Forest K) (a : K) : Network K 0 :=
  (ts.closedFiniteNetwork a).toNetwork

@[simp] theorem Forest.closedNetwork_vertices (ts : Forest K) (a : K) :
    (ts.closedNetwork a).shape.vertices = 1 + ts.vertices := by
  change Fintype.card (Unit ⊕ ts.Vertex) = _
  simp [ts.card_vertex]

@[simp] theorem Forest.closedNetwork_edges (ts : Forest K) (a : K) :
    (ts.closedNetwork a).shape.edges = ts.edges := ts.card_edge

@[simp] theorem Forest.closedNetwork_edge (ts : Forest K) (a : K)
    (e : Fin (ts.closedNetwork a).shape.edges) :
    (ts.closedNetwork a).edge e = Signature.disequality := rfl

/-- Exactly the one-hot signatures of the represented root and descendants. -/
theorem Forest.closedLabel_oneHot (ts : Forest K) (a : K) (v : ts.ClosedVertex) :
    Signature.OneHot (ts.closedLabel a v) := by
  cases v with
  | inl u => exact table_oneHot a ts.coefficients
  | inr v => exact ts.label_oneHot v

theorem Forest.closedNetwork_oneHot (ts : Forest K) (a : K)
    (v : Fin (ts.closedNetwork a).shape.vertices) :
    Signature.OneHot ((ts.closedNetwork a).vertex v) :=
  ts.closedLabel_oneHot a ((Fintype.equivFin ts.ClosedVertex).symm v)

/-- The closed root term is exactly the previously proved unoccupied-parent term.
The virtual parent coefficient is immaterial and no extra vertex is introduced. -/
theorem Forest.closedTerm (ts : Forest K) (a b : K) (x : ts.Choice) :
    table a ts.coefficients (ts.selection x) * ts.weight x =
      (Tree.node a b ts).weight false x := by
  rw [table, ts.weight_selection, ts.prod_selection]
  simp only [Tree.weight, Bool.false_eq_true, ↓reduceIte, zero_add]
  split <;> simp_all

/-- Equality of the genuine closed finite graph sum and the rooted-tree sum. -/
theorem Forest.denote_closedFiniteNetwork (ts : Forest K) (a b : K) :
    (ts.closedFiniteNetwork a).denote Fin.elim0 = (Tree.node a b ts).denote false := by
  classical
  change (FiniteNetwork.mk ts.closedArity ts.closedPortEquiv (ts.closedLabel a)
    (fun _ => Signature.disequality)).denote _ = _
  rw [FiniteNetwork.denote_disequality_apply]
  unfold Tree.denote
  rw [← ts.choiceEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_sum_type, Fintype.prod_unique]
  change table a ts.coefficients
      (fun i => FiniteNetwork.endpointChoiceAssignment (ts.edgeChoices x)
        (ts.portMap (.inl i))) *
    (∏ v, ts.label v (ts.assignment x v)) = _
  have hroot : (fun i => FiniteNetwork.endpointChoiceAssignment (ts.edgeChoices x)
      (ts.portMap (.inl i))) = ts.selection x := funext (ts.parent_assignment x)
  rw [hroot, ts.prod_label_assignment]
  exact ts.closedTerm a b x

/-- Full actual Network denotation, including a singleton nullary tree. -/
theorem Forest.denote_closedNetwork (ts : Forest K) (a b : K) :
    (ts.closedNetwork a).denote Fin.elim0 = (Tree.node a b ts).denote false := by
  rw [Forest.closedNetwork, FiniteNetwork.denote_toNetwork]
  exact ts.denote_closedFiniteNetwork a b

/-- The root evaluates its child messages with one multiplication and one addition. -/
def Forest.closedProgram (ts : Forest K) (a : K) : Arithmetic K K := do
  let s ← ts.program
  let az ← Arithmetic.mulOp a s.1
  Arithmetic.addOp az s.2

/-- Exact actual arithmetic instruction count, with no virtual parent operation. -/
theorem Forest.closedProgram_run (ts : Forest K) (a : K) :
    (ts.closedProgram a).run =
      (a * ts.eval.1 + ts.eval.2, 3 * ts.vertices + 5 * ts.edges + 2) := by
  simp only [Forest.closedProgram, bind, Arithmetic.run_bind, Forest.program_run,
    Arithmetic.run_mulOp, Arithmetic.run_addOp]

/-- End-to-end executable arithmetic correctness for the actual closed graph. -/
theorem Forest.closedProgram_network_spec (ts : Forest K) (a : K) :
    (ts.closedProgram a).run =
      ((ts.closedNetwork a).denote Fin.elim0,
        3 * (ts.closedNetwork a).shape.vertices + 5 * (ts.closedNetwork a).shape.edges - 1) := by
  rw [ts.closedProgram_run, ts.denote_closedNetwork a 0, Tree.denote_false,
    ts.eval_correct, ts.closedNetwork_vertices, ts.closedNetwork_edges]
  congr 1
  omega

/-- The closed graph has one fewer edge than vertices, even for a nullary root. -/
theorem Forest.closedNetwork_edges_add_one (ts : Forest K) (a : K) :
    (ts.closedNetwork a).shape.edges + 1 = (ts.closedNetwork a).shape.vertices := by
  simp only [ts.closedNetwork_edges, ts.closedNetwork_vertices, ts.edges_eq_vertices]
  omega

/-- Linear arithmetic count measured on the actual closed network. -/
theorem Forest.closedProgram_operations_le (ts : Forest K) (a : K) :
    (ts.closedProgram a).run.2 ≤
      5 * ((ts.closedNetwork a).shape.vertices + (ts.closedNetwork a).shape.edges) := by
  rw [ts.closedProgram_network_spec]
  simp only
  omega

end Holant.OneHot
