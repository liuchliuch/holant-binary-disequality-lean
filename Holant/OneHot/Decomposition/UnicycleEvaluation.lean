import Holant.OneHot.Decomposition.FiniteEvaluation
import Holant.OneHot.Decomposition.EdgeConditioning

/-!
# Arbitrary unicyclic multigraph evaluation by an actual surplus edge

The extracted spanning tree identifies an original surplus edge. Conditioning
and deleting that edge gives two genuine closed trees, preserving both distinct
occurrences of a loop and every other original local port. The two existing
closed-tree arithmetic programs are run and their values added. No cycle-core
ordering or supplied pinning gadget is assumed.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Decomposition.RootedSpanning

variable {V E : Type*} {endpoint : E → Bool → V} {root : V}
variable [Fintype V] [Fintype E] (t : RootedSpanning endpoint root)

/-- The equal edge/vertex count supplies an actual original surplus edge. -/
noncomputable def chooseSurplus (h : Fintype.card E = Fintype.card V) : t.Surplus :=
  Classical.choice (Fintype.card_pos_iff.mp (by rw [t.surplus_card_eq_one h]; decide))

end Holant.OneHot.Decomposition.RootedSpanning

namespace Holant.FiniteNetwork

open OneHot OneHot.Decomposition

variable {K V E : Type*} [Fintype V] [Fintype E]
variable (N : FiniteNetwork K V E 0) {root : V} (t : RootedSpanning N.endpoint root)

open scoped Classical

/-- Every selected tree edge survives deletion of any original surplus edge. -/
def remainingParentEdge (e : t.Surplus) (u : {v : V // v ≠ root}) : RemainingEdge e.1 :=
  ⟨t.parentEdge u, by intro h; exact e.2 ⟨u, h⟩⟩

omit [Fintype V] [Fintype E] in
/-- Deleting a surplus edge retains actual connectivity through all original
selected parent edges. No additional connectivity hypothesis is needed. -/
theorem conditionEdge_connected (e : t.Surplus) (a b : Bool) (v : V) :
    Relation.EqvGen (Link (N.conditionEdge e.1 a b).endpoint) root v := by
  exact reachable_map id (N.remainingParentEdge t e) (fun _ _ => rfl) (t.selected_reachable v)

/-- Deleting exactly one original edge decrements the actual edge count by one. -/
theorem remainingEdge_card (e : E) : Fintype.card (RemainingEdge e) + 1 = Fintype.card E := by
  have hcard : Fintype.card (RemainingEdge e) = Fintype.card E - 1 := by
    simp [RemainingEdge, Fintype.card_subtype_compl]
  have hpos : 0 < Fintype.card E := Fintype.card_pos_iff.mpr ⟨e⟩
  omega

variable [CommSemiring K]

/-- Evaluate one of the two literal endpoint-conditioned residual trees. -/
noncomputable def conditionedTreeProgram (e : t.Surplus) (a b : Bool) : Arithmetic K K :=
  (N.conditionEdge e.1 a b).connectedTreeProgram root (N.conditionEdge_connected t e a b)

/-- Correctness and exact arithmetic count of one conditioned residual graph. -/
theorem conditionedTreeProgram_spec (e : t.Surplus) (a b : Bool)
    (hcycle : Fintype.card E = Fintype.card V)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.conditionedTreeProgram t e a b).run =
      ((N.conditionEdge e.1 a b).denote Fin.elim0,
        3 * Fintype.card V + 5 * Fintype.card (RemainingEdge e.1) - 1) :=
  (N.conditionEdge e.1 a b).connectedTreeProgram_spec root
    (N.conditionEdge_connected t e a b)
    ((remainingEdge_card e.1).trans hcycle)
    (N.conditionEdge_oneHot e.1 a b hf)
    (fun d => hX d.1)

/-- Literal arithmetic program: evaluate the two residual trees, then add once. -/
noncomputable def spanningUnicycleProgram (e : t.Surplus) : Arithmetic K K := do
  let x ← N.conditionedTreeProgram t e false true
  let y ← N.conditionedTreeProgram t e true false
  Arithmetic.addOp x y

/-- Exact denotation and arithmetic instructions for a genuine unicyclic input,
including loops, parallel edges and attached trees with zero coefficients. -/
theorem spanningUnicycleProgram_spec (e : t.Surplus)
    (hcycle : Fintype.card E = Fintype.card V)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.spanningUnicycleProgram t e).run =
      (N.denote Fin.elim0, 6 * Fintype.card V + 10 * Fintype.card E - 11) := by
  rw [spanningUnicycleProgram]
  simp only [bind, Arithmetic.run_bind,
    N.conditionedTreeProgram_spec t e false true hcycle hf hX,
    N.conditionedTreeProgram_spec t e true false hcycle hf hX, Arithmetic.run_addOp]
  rw [N.denote_eq_two_conditionEdge e.1 (hX e.1) Fin.elim0]
  have he := remainingEdge_card e.1
  have hv : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  congr 1
  omega

/-- Obtain the spanning structure and its surplus edge from input connectivity
and actual cardinalities alone. -/
noncomputable def unicycleProgram (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (hcycle : Fintype.card E = Fintype.card V) : Arithmetic K K :=
  let t := extractRootedSpanning N.endpoint root connected
  N.spanningUnicycleProgram t (t.chooseSurplus hcycle)

/-- Full arbitrary connected-unicycle arithmetic specification, without a
supplied cycle, spanning tree, edge ordering or semantic decomposition. -/
theorem unicycleProgram_spec (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (hcycle : Fintype.card E = Fintype.card V)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.unicycleProgram root connected hcycle).run =
      (N.denote Fin.elim0, 6 * Fintype.card V + 10 * Fintype.card E - 11) :=
  N.spanningUnicycleProgram_spec (extractRootedSpanning N.endpoint root connected)
    ((extractRootedSpanning N.endpoint root connected).chooseSurplus hcycle) hcycle hf hX

/-- Linear semiring-operation bound measured on the original input multigraph. -/
theorem unicycleProgram_operations_le (root : V)
    (connected : ∀ v, Relation.EqvGen (Link N.endpoint) root v)
    (hcycle : Fintype.card E = Fintype.card V)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.unicycleProgram root connected hcycle).run.2 ≤
      10 * (Fintype.card V + Fintype.card E) := by
  rw [N.unicycleProgram_spec root connected hcycle hf hX]
  simp only
  omega

end Holant.FiniteNetwork
