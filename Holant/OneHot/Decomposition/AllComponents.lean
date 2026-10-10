import Holant.OneHot.Decomposition.ConnectedEvaluation
import Holant.OneHot.Decomposition.Presentation

/-!
# Arithmetic evaluation of arbitrary original one-hot multigraphs

All genuine connected components are extracted from the original port graph,
evaluated by proved dense/tree/unicycle cases, and multiplied by an explicit
arithmetic program. The final instruction bound is measured on the original
vertex and edge counts, including empty and nullary components. This semantic
construction does not yet prove effective graph preprocessing or machine-level
fixed-number-field bit time.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Arithmetic

variable {K : Type*} [CommSemiring K]

/-- Execute a finite family of arithmetic programs and multiply their outputs. -/
def finiteProduct : {n : ℕ} → (Fin n → Arithmetic K K) → Arithmetic K K
  | 0, _ => .pure 1
  | n + 1, p => do
    let x ← p 0
    let y ← finiteProduct (fun i : Fin n => p i.succ)
    mulOp x y

/-- The product program counts every component instruction plus one actual
multiplication per component. Empty input is the literal constant-one program. -/
theorem finiteProduct_run {n : ℕ} (p : Fin n → Arithmetic K K) :
    (finiteProduct p).run =
      (∏ i, (p i).run.1, (∑ i, (p i).run.2) + n) := by
  induction n with
  | zero => simp [finiteProduct]
  | succ n ih =>
    simp only [finiteProduct, Bind.bind, run_bind, ih, run_mulOp,
      Fin.prod_univ_succ, Fin.sum_univ_succ]
    congr 1
    omega

end Holant.OneHot.Arithmetic

namespace Holant.Network

open OneHot OneHot.Decomposition

variable {K : Type*} [CommSemiring K] (N : Network K 0)

open scoped Classical

omit [CommSemiring K] in
/-- The finite component presentation has precisely its original endpoint vertices. -/
theorem componentFiniteNetwork_endpoint (c : N.shape.Component)
    (e : N.shape.ComponentEdge c) (b : Bool) :
    (N.componentFiniteNetwork c).endpoint e b = N.shape.componentEndpoint c e b := rfl

omit [CommSemiring K] in
/-- Connectivity holds using only the component's own actual restricted edges. -/
theorem componentFiniteNetwork_connected (c : N.shape.Component)
    (v : N.shape.ComponentVertex c) :
    Relation.EqvGen (Link (N.componentFiniteNetwork c).endpoint) (N.shape.componentRoot c) v := by
  change Relation.EqvGen (Link (N.shape.componentEndpoint c)) (N.shape.componentRoot c) v
  exact N.shape.componentEndpoint_connected c (N.shape.componentRoot c) v

/-- The actual arithmetic program of one extracted connected component. -/
noncomputable def componentProgram (c : N.shape.Component) : Arithmetic K K :=
  (N.componentFiniteNetwork c).connectedProgram (N.shape.componentRoot c)
    (N.componentFiniteNetwork_connected c)

/-- Every component program evaluates its original restricted labels and counts. -/
theorem componentProgram_spec (c : N.shape.Component)
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (N.componentProgram c).run.1 = (N.componentFiniteNetwork c).denote Fin.elim0 ∧
      (N.componentProgram c).run.2 ≤
        10 * (Fintype.card (N.shape.ComponentVertex c) + Fintype.card (N.shape.ComponentEdge c)) :=
  (N.componentFiniteNetwork c).connectedProgram_spec (N.shape.componentRoot c)
    (N.componentFiniteNetwork_connected c) (fun v => hf v.1) (fun e => hX e.1)

/-- Multiply the genuine component programs, including all isolated nullary vertices. -/
noncomputable def oneHotProgram : Arithmetic K K :=
  Arithmetic.finiteProduct (fun i : Fin (Fintype.card N.shape.Component) =>
    N.componentProgram ((Fintype.equivFin N.shape.Component).symm i))

/-- Complete original-network denotation and a linear actual semiring-instruction
bound. There is no assumed semantic decomposition or discarded graph incidence. -/
theorem oneHotProgram_spec
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    N.oneHotProgram.run.1 = N.denote Fin.elim0 ∧
      N.oneHotProgram.run.2 ≤ 11 * (N.shape.vertices + N.shape.edges) := by
  rw [oneHotProgram, Arithmetic.finiteProduct_run]
  simp only
  let en := (Fintype.equivFin N.shape.Component).symm
  constructor
  · calc
      (∏ i, (N.componentProgram (en i)).run.1) =
          ∏ i, (N.componentFiniteNetwork (en i)).denote Fin.elim0 := by
        apply Finset.prod_congr rfl
        intro i _
        exact (N.componentProgram_spec (en i) hf hX).1
      _ = ∏ c, (N.componentFiniteNetwork c).denote Fin.elim0 := en.prod_comp (fun c => (N.componentFiniteNetwork c).denote Fin.elim0)
      _ = N.denote Fin.elim0 := (N.denote_eq_prod_componentFiniteNetwork Fin.elim0).symm
  · have hcost : (∑ i, (N.componentProgram (en i)).run.2) ≤
        ∑ i, 10 * (Fintype.card (N.shape.ComponentVertex (en i)) +
          Fintype.card (N.shape.ComponentEdge (en i))) := by
      apply Finset.sum_le_sum
      intro i _
      exact (N.componentProgram_spec (en i) hf hX).2
    have hsum : (∑ i, 10 * (Fintype.card (N.shape.ComponentVertex (en i)) +
        Fintype.card (N.shape.ComponentEdge (en i)))) =
        10 * (N.shape.vertices + N.shape.edges) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        en.sum_comp (fun c => Fintype.card (N.shape.ComponentVertex c)),
        en.sum_comp (fun c => Fintype.card (N.shape.ComponentEdge c)),
        N.shape.sum_componentVertex_card, N.shape.sum_componentEdge_card]
    rw [hsum] at hcost
    have hc : Fintype.card N.shape.Component ≤ N.shape.vertices := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
        N.shape.componentOf N.shape.componentOf_surjective
    dsimp only [en] at hcost
    omega

/-- Signature-level correctness, since a closed network has one boundary word. -/
theorem oneHotProgram_denote
    (hf : ∀ v, Signature.OneHot (N.vertex v))
    (hX : ∀ e, N.edge e = Signature.disequality) :
    (fun _ : Fin 0 → Bool => N.oneHotProgram.run.1) = N.denote := by
  funext x
  have hx : x = Fin.elim0 := funext (fun i => Fin.elim0 i)
  subst x
  exact (N.oneHotProgram_spec hf hX).1

end Holant.Network
