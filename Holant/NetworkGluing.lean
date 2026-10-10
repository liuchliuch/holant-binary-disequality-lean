import Holant.NetworkGluing.Finite
import Holant.BoundaryAction

/-!
Actual graph gluing for two networks with ordinary exposed ports. The vertices
are their disjoint union; the old internal edges are retained and one new edge
joins each matching pair of boundary occurrences, with the left port at the
false end and the right port at the true end. Arbitrary (including asymmetric)
new kernels are supported. This does not claim arbitrary vertex replacement in
a context with paired free stubs; that larger model is `OpenNetwork`.
-/

namespace Holant.Network

variable {K : Type*} {n : ℕ}

/-- Old left edges, old right edges, and the new edges, in distinct summands. -/
abbrev GluedEdges (L R : Network K n) :=
  (Fin L.shape.edges ⊕ Fin R.shape.edges) ⊕ Fin n

/-- The incidence bijection that turns matching ordinary boundary occurrences
into the two independently labelled ends of a new edge. -/
def gluePorts (EL ER : Type*) (n : ℕ) :
    ((Fin n ⊕ (EL × Bool)) ⊕ (Fin n ⊕ (ER × Bool))) ≃
      (((EL ⊕ ER) ⊕ Fin n) × Bool) where
  toFun
    | .inl (.inl i) => (.inr i, false)
    | .inr (.inl i) => (.inr i, true)
    | .inl (.inr (e, b)) => (.inl (.inl e), b)
    | .inr (.inr (e, b)) => (.inl (.inr e), b)
  invFun
    | (.inr i, false) => .inl (.inl i)
    | (.inr i, true) => .inr (.inl i)
    | (.inl (.inl e), b) => .inl (.inr (e, b))
    | (.inl (.inr e), b) => .inr (.inr (e, b))
  left_inv := by rintro ((i | ⟨e, b⟩) | (i | ⟨e, b⟩)) <;> rfl
  right_inv := by rintro ⟨((e | e) | i), b⟩ <;> cases b <;> rfl

/-- The genuine glued graph before enumerating its finite vertex and edge sets. -/
def glueFinite (L R : Network K n) (W : Fin n → Bool → Bool → K) :
    FiniteNetwork K (Fin L.shape.vertices ⊕ Fin R.shape.vertices) (GluedEdges L R) 0 where
  arity := Sum.elim L.shape.arity R.shape.arity
  ports := (Equiv.sumSigmaDistrib (fun v => Fin (Sum.elim L.shape.arity R.shape.arity v))).trans
    ((Equiv.sumCongr L.shape.ports R.shape.ports).trans
      ((gluePorts _ _ n).trans (Equiv.emptySum (Fin 0) _).symm))
  vertex := fun v => match v with
    | .inl l => L.vertex l
    | .inr r => R.vertex r
  edge
    | .inl (.inl e) => L.edge e
    | .inl (.inr e) => R.edge e
    | .inr i => W i

/-- Close two actual networks by adding one edge per matching boundary port. -/
noncomputable def glue (L R : Network K n) (W : Fin n → Bool → Bool → K) : Network K 0 :=
  (glueFinite L R W).toNetwork

@[simp] theorem glue_vertices (L R : Network K n) (W : Fin n → Bool → Bool → K) :
    (glue L R W).shape.vertices = L.shape.vertices + R.shape.vertices := by
  simp [glue, FiniteNetwork.toNetwork]

@[simp] theorem glue_edges (L R : Network K n) (W : Fin n → Bool → Bool → K) :
    (glue L R W).shape.edges = L.shape.edges + R.shape.edges + n := by
  simp [glue, FiniteNetwork.toNetwork, GluedEdges]

/-- The edge enumeration preserves all original and added kernel labels. -/
@[simp] theorem glue_edge_label (L R : Network K n) (W : Fin n → Bool → Bool → K)
    (e : GluedEdges L R) :
    (glue L R W).edge ((Fintype.equivFin (GluedEdges L R)) e) =
      (glueFinite L R W).edge e := by
  simp [glue, FiniteNetwork.toNetwork]

/-- Identify a port occurrence of the enumerated output with its original
left or right occurrence. This also records which vertex and which ordered
port it came from. -/
noncomputable def gluePortCopies (L R : Network K n) (W : Fin n → Bool → Bool → K) :
    (Σ v : Fin (glue L R W).shape.vertices, Fin ((glue L R W).shape.arity v)) ≃
      ((Σ v : Fin L.shape.vertices, Fin (L.shape.arity v)) ⊕
        (Σ v : Fin R.shape.vertices, Fin (R.shape.arity v))) :=
  (Equiv.sigmaCongrLeft (Fintype.equivFin
    (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm).trans
    (Equiv.sumSigmaDistrib (fun v => Fin (Sum.elim L.shape.arity R.shape.arity v)))

set_option backward.isDefEq.respectTransparency false in
/-- Every old left endpoint has exactly the same vertex and ordered port in
the glued graph, under the explicit disjoint-union identification. -/
theorem glue_old_left_endpoint (L R : Network K n) (W : Fin n → Bool → Bool → K)
    (e : Fin L.shape.edges) (a : Bool) :
    gluePortCopies L R W ((glue L R W).shape.ports.symm
      (.inr ((Fintype.equivFin (GluedEdges L R)) (.inl (.inl e)), a))) =
        .inl (L.shape.ports.symm (.inr (e, a))) := by
  simp [gluePortCopies, glue, FiniteNetwork.toNetwork, glueFinite, gluePorts, Equiv.trans_apply]
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- Old right edges are retained independently, even if they are parallel or
loops, and are never identified with left or new edges. -/
theorem glue_old_right_endpoint (L R : Network K n) (W : Fin n → Bool → Bool → K)
    (e : Fin R.shape.edges) (a : Bool) :
    gluePortCopies L R W ((glue L R W).shape.ports.symm
      (.inr ((Fintype.equivFin (GluedEdges L R)) (.inl (.inr e)), a))) =
        .inr (R.shape.ports.symm (.inr (e, a))) := by
  simp [gluePortCopies, glue, FiniteNetwork.toNetwork, glueFinite, gluePorts, Equiv.trans_apply]
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- The false endpoint of new edge `i` is precisely left boundary port `i`. -/
theorem glue_new_left_endpoint (L R : Network K n) (W : Fin n → Bool → Bool → K)
    (i : Fin n) :
    gluePortCopies L R W ((glue L R W).shape.ports.symm
      (.inr ((Fintype.equivFin (GluedEdges L R)) (.inr i), false))) =
        .inl (L.shape.ports.symm (.inl i)) := by
  simp [gluePortCopies, glue, FiniteNetwork.toNetwork, glueFinite, gluePorts, Equiv.trans_apply]
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- The true endpoint of new edge `i` is precisely right boundary port `i`.
This orientation matters for asymmetric kernels. -/
theorem glue_new_right_endpoint (L R : Network K n) (W : Fin n → Bool → Bool → K)
    (i : Fin n) :
    gluePortCopies L R W ((glue L R W).shape.ports.symm
      (.inr ((Fintype.equivFin (GluedEdges L R)) (.inr i), true))) =
        .inr (R.shape.ports.symm (.inl i)) := by
  simp [gluePortCopies, glue, FiniteNetwork.toNetwork, glueFinite, gluePorts, Equiv.trans_apply]
  exact Equiv.apply_symm_apply _ _

/-- A glued edge-end assignment consists of two independent boundary words and
all old internal edge-end bits. No loop ends or boundary bits are identified. -/
def glueAssignments (L R : Network K n) :
    ((GluedEdges L R × Bool) → Bool) ≃
      ((Fin n → Bool) × ((Fin n → Bool) ×
        (((Fin L.shape.edges × Bool) → Bool) × ((Fin R.shape.edges × Bool) → Bool)))) where
  toFun := fun z => (fun i => z (.inr i, false), fun i => z (.inr i, true),
    fun q => z (.inl (.inl q.1), q.2), fun q => z (.inl (.inr q.1), q.2))
  invFun := fun p q => match q with
    | (.inr i, false) => p.1 i
    | (.inr i, true) => p.2.1 i
    | (.inl (.inl e), b) => p.2.2.1 (e, b)
    | (.inl (.inr e), b) => p.2.2.2 (e, b)
  left_inv := by
    intro z
    funext q
    rcases q with ⟨((e | e) | i), b⟩ <;> cases b <;> rfl
  right_inv := by intro p; rfl

variable [CommSemiring K]

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Exact graph-level finite-boundary gluing: old internal sums, all scalar
components, and the specified oriented kernels are retained without normalization. -/
theorem denote_glue (L R : Network K n) (W : Fin n → Bool → Bool → K)
    (b : Fin 0 → Bool) :
    (glue L R W).denote b =
      ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
        L.denote x * R.denote y * ∏ i, W i (x i) (y i) := by
  classical
  let : DecidableEq (GluedEdges L R) := Classical.decEq _
  rw [glue, FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  change (∑ z : (GluedEdges L R × Bool) → Bool,
    (∏ v, (glueFinite L R W).vertex v (fun i => Sum.elim b z ((glueFinite L R W).ports ⟨v, i⟩))) *
    ∏ e, (glueFinite L R W).edge e (z (e, false)) (z (e, true))) = _
  rw [← (glueAssignments L R).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [denote, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  dsimp only [glueFinite]
  simp only [Fintype.prod_sum_type]
  have hl : (fun (v : Fin L.shape.vertices) (i : Fin (L.shape.arity v)) =>
      Sum.elim b ((glueAssignments L R).symm (x, y, zL, zR))
        ((glueFinite L R W).ports ⟨.inl v, i⟩)) =
      L.shape.assignment x zL := by
    funext v i
    dsimp [glueFinite, NetworkShape.assignment]
    change Sum.elim b ((glueAssignments L R).symm (x, y, zL, zR))
      (.inr (gluePorts _ _ n (.inl (L.shape.ports ⟨v, i⟩)))) = _
    cases L.shape.ports ⟨v, i⟩ <;> rfl
  have hr : (fun (v : Fin R.shape.vertices) (i : Fin (R.shape.arity v)) =>
      Sum.elim b ((glueAssignments L R).symm (x, y, zL, zR))
        ((glueFinite L R W).ports ⟨.inr v, i⟩)) =
      R.shape.assignment y zR := by
    funext v i
    dsimp [glueFinite, NetworkShape.assignment]
    change Sum.elim b ((glueAssignments L R).symm (x, y, zL, zR))
      (.inr (gluePorts _ _ n (.inr (R.shape.ports ⟨v, i⟩)))) = _
    cases R.shape.ports ⟨v, i⟩ <;> rfl
  dsimp [glueAssignments]
  dsimp [glueFinite, glueAssignments] at hl hr
  simp only [congrFun₂ hl, congrFun₂ hr]
  ac_rfl

/-- Ordinary equality wires identify the two boundary words and give a
bilinear pairing, without conjugation or any discarded scalar factor. -/
theorem denote_glue_equality (L R : Network K n) (b : Fin 0 → Bool) :
    (glue L R (fun _ => Signature.equality)).denote b =
      ∑ x : Fin n → Bool, L.denote x * R.denote x := by
  classical
  rw [denote_glue]
  simp only [Signature.prod_equality]
  simp

/-- With an empty boundary, closing by gluing is disjoint union and multiplies
closed partition functions, including nonunit nullary components. -/
theorem denote_glue_nullary (L R : Network K 0) (W : Fin 0 → Bool → Bool → K)
    (b : Fin 0 → Bool) :
    (glue L R W).denote b = L.denote b * R.denote b := by
  rw [denote_glue]
  simp only [Fintype.prod_empty, mul_one, Fintype.sum_unique]
  congr 1 <;> exact congrArg _ (Subsingleton.elim _ _)

end Holant.Network
