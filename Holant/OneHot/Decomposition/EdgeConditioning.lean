import Holant.OneHot.Decomposition.EndpointTransport
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Deleting one actual edge and conditioning its two original occurrences. Every
vertex survives, including isolated nullary vertices; a loop removes two distinct
local occurrences. Surviving ports are enumerated in their original order.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.FiniteNetwork

variable {K V E : Type*}

/-- Precisely the old edges other than the selected edge, with unchanged orientation. -/
abbrev RemainingEdge (e : E) := {d : E // d ≠ e}

/-- The surviving original local positions. -/
abbrev RemainingPort (N : FiniteNetwork K V E 0) (e : E) (v : V) :=
  {i : Fin (N.arity v) // (N.closedPorts ⟨v, i⟩).1 ≠ e}

noncomputable def remainingPorts (N : FiniteNetwork K V E 0) (e : E) (v : V) :
    Finset (Fin (N.arity v)) := by
  classical
  exact Finset.univ.filter (fun i => (N.closedPorts ⟨v, i⟩).1 ≠ e)

@[simp] theorem mem_remainingPorts (N : FiniteNetwork K V E 0) (e : E) (v : V)
    (i : Fin (N.arity v)) : i ∈ N.remainingPorts e v ↔ (N.closedPorts ⟨v, i⟩).1 ≠ e := by
  classical
  simp [remainingPorts]

/-- Increasing enumeration, rather than an arbitrary permutation of the survivors. -/
noncomputable def remainingPortEquiv (N : FiniteNetwork K V E 0) (e : E) (v : V) :
    Fin (N.remainingPorts e v).card ≃ N.RemainingPort e v :=
  ((N.remainingPorts e v).orderIsoOfFin rfl).toEquiv.trans
    (Equiv.subtypeEquivRight (fun i => N.mem_remainingPorts e v i))

theorem remainingPortEquiv_strictMono (N : FiniteNetwork K V E 0) (e : E) (v : V) :
    StrictMono (fun j => (N.remainingPortEquiv e v j).1) :=
  ((N.remainingPorts e v).orderEmbOfFin rfl).strictMono

/-- Restrict incidence before enumerating. Both occurrences of the deleted edge
are absent, even when the edge is a loop. -/
def remainingClosedPorts (N : FiniteNetwork K V E 0) (e : E) :
    (Σ v : V, N.RemainingPort e v) ≃ (RemainingEdge e × Bool) where
  toFun p := (⟨(N.closedPorts ⟨p.1, p.2.1⟩).1, p.2.2⟩,
    (N.closedPorts ⟨p.1, p.2.1⟩).2)
  invFun q := ⟨(N.closedPorts.symm (q.1.1, q.2)).1,
    ⟨(N.closedPorts.symm (q.1.1, q.2)).2, by
      simpa only [Sigma.eta, Equiv.apply_symm_apply] using q.1.2⟩⟩
  left_inv p := by
    let forget : (Σ v : V, N.RemainingPort e v) → (Σ v : V, Fin (N.arity v)) :=
      fun p => ⟨p.1, p.2.1⟩
    have hinj : Function.Injective forget := by
      rintro ⟨v, i, hi⟩ ⟨w, j, hj⟩ h
      dsimp [forget] at h
      cases h
      rfl
    apply hinj
    exact N.closedPorts.symm_apply_apply ⟨p.1, p.2.1⟩
  right_inv q := by
    dsimp only
    simp only [Sigma.eta, Equiv.apply_symm_apply]

/-- Exactly two original occurrences are removed, distinguished by their
original orientation even when both occur at the same vertex. -/
def removedOccurrencesEquiv (N : FiniteNetwork K V E 0) (e : E) :
    {p : Σ v : V, Fin (N.arity v) // (N.closedPorts p).1 = e} ≃ Bool where
  toFun p := (N.closedPorts p.1).2
  invFun c := ⟨N.closedPorts.symm (e, c), by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply N.closedPorts.injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext p.2.symm rfl
  right_inv c := by simp

@[simp] theorem removedOccurrences_card (N : FiniteNetwork K V E 0) (e : E) :
    Nat.card {p : Σ v : V, Fin (N.arity v) // (N.closedPorts p).1 = e} = 2 := by
  rw [Nat.card_congr (N.removedOccurrencesEquiv e)]
  simp

/-- Put the chosen endpoint bits back into the two removed local occurrences. -/
noncomputable def conditionWord (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (v : V) (x : Fin (N.remainingPorts e v).card → Bool) :
    Fin (N.arity v) → Bool := by
  classical
  exact fun i => if h : (N.closedPorts ⟨v, i⟩).1 = e then
    (if (N.closedPorts ⟨v, i⟩).2 then b else a)
    else x ((N.remainingPortEquiv e v).symm ⟨i, h⟩)

/-- A genuine residual graph, with every old vertex and every remaining edge. -/
noncomputable def conditionEdge (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) : FiniteNetwork K V (RemainingEdge e) 0 where
  arity v := (N.remainingPorts e v).card
  ports := (Equiv.sigmaCongrRight (N.remainingPortEquiv e)).trans
    ((N.remainingClosedPorts e).trans (Equiv.emptySum (Fin 0) _).symm)
  vertex v x := N.vertex v (N.conditionWord e a b v x)
  edge d := N.edge d.1

@[simp] theorem conditionEdge_arity (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (v : V) : (N.conditionEdge e a b).arity v = (N.remainingPorts e v).card := rfl

@[simp] theorem conditionEdge_edge (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (d : RemainingEdge e) : (N.conditionEdge e a b).edge d = N.edge d.1 := rfl

/-- Exact oriented endpoint identity at each surviving local position. -/
theorem conditionEdge_closedPorts (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (v : V) (j : Fin (N.remainingPorts e v).card) :
    let q := (N.conditionEdge e a b).closedPorts ⟨v, j⟩
    (q.1.1, q.2) = N.closedPorts ⟨v, (N.remainingPortEquiv e v j).1⟩ := rfl

/-- A nullary old vertex remains nullary after deletion. -/
theorem conditionEdge_nullary_arity (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (v : V) (hzero : N.arity v = 0) :
    (N.conditionEdge e a b).arity v = 0 := by
  change (N.remainingPorts e v).card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i
  exact Fin.elim0 (Fin.cast hzero i)

/-- The actual scalar label at any old nullary vertex is untouched. -/
theorem conditionEdge_nullary_vertex (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (v : V) (hzero : N.arity v = 0)
    (x : Fin (N.remainingPorts e v).card → Bool) (y : Fin (N.arity v) → Bool) :
    (N.conditionEdge e a b).vertex v x = N.vertex v y := by
  apply congrArg (N.vertex v)
  funext i
  exact Fin.elim0 (Fin.cast hzero i)

/-- Split a full assignment into the selected edge's two independent bits and
the assignment of all remaining edge ends. -/
noncomputable def edgeConditionAssignments (e : E) :
    ((E × Bool) → Bool) ≃ (Bool × Bool × ((RemainingEdge e × Bool) → Bool)) := by
  classical
  exact {
    toFun z := (z (e, false), z (e, true), fun q => z (q.1.1, q.2))
    invFun p q := if h : q.1 = e then (if q.2 then p.2.1 else p.1)
      else p.2.2 (⟨q.1, h⟩, q.2)
    left_inv z := by
      funext q
      rcases q with ⟨d, c⟩
      by_cases h : d = e
      · subst d; cases c <;> simp
      · simp [h]
    right_inv p := by
      rcases p with ⟨a, b, z⟩
      apply Prod.ext
      · simp
      · apply Prod.ext
        · simp
        · funext q
          simp [q.1.2] }

end Holant.FiniteNetwork

namespace Holant.FiniteNetwork

variable {K V E : Type*}

@[simp] theorem conditionWord_remaining (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (v : V) (x : Fin (N.remainingPorts e v).card → Bool)
    (j : Fin (N.remainingPorts e v).card) :
    N.conditionWord e a b v x (N.remainingPortEquiv e v j).1 = x j := by
  classical
  simp [conditionWord, (N.remainingPortEquiv e v j).2]

/-- Each removed occurrence receives its own selected bit, including the two
occurrences at a common vertex of a loop. -/
@[simp] theorem conditionWord_selectedEndpoint (N : FiniteNetwork K V E 0) (e : E)
    (a b c : Bool)
    (x : Fin (N.remainingPorts e (N.endpoint e c)).card → Bool) :
    N.conditionWord e a b (N.endpoint e c) x (N.closedPorts.symm (e, c)).2 =
      if c then b else a := by
  classical
  simp [conditionWord, endpoint]

/-- The oriented endpoint vertices are exactly their original vertices. -/
@[simp] theorem conditionEdge_endpoint (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (d : RemainingEdge e) (c : Bool) :
    (N.conditionEdge e a b).endpoint d c = N.endpoint d.1 c := rfl

/-- Reinserted bits can only increase Hamming weight. -/
theorem weight_le_conditionWord (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (v : V) (x : Fin (N.remainingPorts e v).card → Bool) :
    weight x ≤ weight (N.conditionWord e a b v x) := by
  classical
  let f : Fin (N.arity v) → ℕ := fun i => if N.conditionWord e a b v x i then 1 else 0
  have h : weight x = ∑ i : N.RemainingPort e v, f i.1 := by
    rw [← (N.remainingPortEquiv e v).sum_comp]
    simp only [f, conditionWord_remaining, weight]
  rw [h]
  exact le_trans (Nat.le_add_right _ _)
    (le_of_eq (Fintype.sum_subtype_add_sum_subtype
      (fun i : Fin (N.arity v) => (N.closedPorts ⟨v, i⟩).1 ≠ e) f))

/-- Conditioning the actual table preserves one-hot support. This does not add
or assume any freely supplied pinning signatures. -/
theorem conditionEdge_oneHot [Zero K] (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (hf : ∀ v, Signature.OneHot (N.vertex v)) (v : V) :
    Signature.OneHot ((N.conditionEdge e a b).vertex v) := by
  intro x hx
  exact hf v _ (lt_of_lt_of_le hx (N.weight_le_conditionWord e a b v x))

@[simp] theorem sumElim_closedPorts (N : FiniteNetwork K V E 0)
    (x : Fin 0 → Bool) (z : (E × Bool) → Bool) (v : V) (i : Fin (N.arity v)) :
    Sum.elim x z (N.ports ⟨v, i⟩) = z (N.closedPorts ⟨v, i⟩) := by
  dsimp [closedPorts]
  cases h : N.ports ⟨v, i⟩ with
  | inl a => exact Fin.elim0 a
  | inr q => rfl

/-- Pointwise assignment compatibility for the genuine residual graph. -/
theorem conditionEdge_assignment (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (z : (RemainingEdge e × Bool) → Bool) (v : V) :
    N.conditionWord e a b v
      (fun j => z ((N.conditionEdge e a b).closedPorts ⟨v, j⟩)) =
    fun i => (edgeConditionAssignments e).symm (a, b, z) (N.closedPorts ⟨v, i⟩) := by
  classical
  funext i
  by_cases h : (N.closedPorts ⟨v, i⟩).1 = e
  · simp [conditionWord, edgeConditionAssignments, h]
  · simp only [conditionWord, h, ↓reduceDIte, edgeConditionAssignments, Equiv.coe_fn_symm_mk]
    congr 1
    change (N.remainingClosedPorts e)
      ⟨v, N.remainingPortEquiv e v ((N.remainingPortEquiv e v).symm ⟨i, h⟩)⟩ = _
    rw [Equiv.apply_symm_apply]
    rfl

variable [Fintype V] [Fintype E] [CommSemiring K]

open scoped Classical in
omit [Fintype V] in
/-- Remove exactly one factor from the literal original edge product. -/
theorem edgeCondition_product (N : FiniteNetwork K V E 0) (e : E)
    (a b : Bool) (z : (RemainingEdge e × Bool) → Bool) :
    (∏ d : E, N.edge d
      ((edgeConditionAssignments e).symm (a, b, z) (d, false))
      ((edgeConditionAssignments e).symm (a, b, z) (d, true))) =
    N.edge e a b * ∏ d : RemainingEdge e, N.edge d.1 (z (d, false)) (z (d, true)) := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun d : E => d = e)]
  apply congrArg₂ (· * ·)
  · calc
      _ = ∏ _d : {d : E // d = e}, N.edge e a b := by
        apply Finset.prod_congr (by ext; simp)
        intro d _
        simp [edgeConditionAssignments, d.2]
      _ = N.edge e a b := by simp
  · apply Finset.prod_congr (by ext; simp)
    intro d _
    simp [edgeConditionAssignments, d.2]


open scoped Classical in
/-- Exact edge conditioning of the actual assignment sum, for an arbitrary
oriented edge tensor, including selected loops and parallel edges. -/
theorem denote_eq_sum_conditionEdge (N : FiniteNetwork K V E 0) (e : E)
    (x : Fin 0 → Bool) :
    N.denote x = ∑ a : Bool, ∑ b : Bool,
      N.edge e a b * (N.conditionEdge e a b).denote x := by
  classical
  unfold denote
  rw [← (edgeConditionAssignments e).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  apply Finset.sum_congr (by ext; simp)
  intro b _
  apply Finset.sum_congr (by ext; simp)
  intro z _
  simp only [sumElim_closedPorts, conditionEdge_edge]
  rw [edgeCondition_product]
  have hv : (∏ v, (N.conditionEdge e a b).vertex v
      (fun i => z ((N.conditionEdge e a b).closedPorts ⟨v, i⟩))) =
      ∏ v, N.vertex v (fun i => (edgeConditionAssignments e).symm (a, b, z)
        (N.closedPorts ⟨v, i⟩)) := by
    apply Finset.prod_congr (by ext; simp)
    intro v _
    exact congrArg (N.vertex v) (N.conditionEdge_assignment e a b z v)
  rw [hv]
  ac_rfl

open scoped Classical in
/-- Native X leaves precisely the two opposite endpoint conditions. -/
theorem denote_eq_two_conditionEdge (N : FiniteNetwork K V E 0) (e : E)
    (hX : N.edge e = Signature.disequality) (x : Fin 0 → Bool) :
    N.denote x = (N.conditionEdge e false true).denote x +
      (N.conditionEdge e true false).denote x := by
  classical
  rw [N.denote_eq_sum_conditionEdge e x, hX]
  simp [Signature.disequality, add_comm]

end Holant.FiniteNetwork

namespace Holant.Network

variable {K : Type*}

/-- Enumerate the literal residual finite graph as an ordinary closed Network. -/
noncomputable def conditionEdge (N : Network K 0) (e : Fin N.shape.edges)
    (a b : Bool) : Network K 0 :=
  (N.asFinite.conditionEdge e a b).toNetwork

@[simp] theorem conditionEdge_vertices (N : Network K 0) (e : Fin N.shape.edges)
    (a b : Bool) : (N.conditionEdge e a b).shape.vertices = N.shape.vertices := by
  simp [conditionEdge, FiniteNetwork.toNetwork]

/-- Every original surviving edge is present exactly once. -/
@[simp] theorem conditionEdge_edges (N : Network K 0) (e : Fin N.shape.edges)
    (a b : Bool) : (N.conditionEdge e a b).shape.edges = N.shape.edges - 1 := by
  classical
  simp [conditionEdge, FiniteNetwork.toNetwork, FiniteNetwork.RemainingEdge,
    Fintype.card_subtype_compl]

variable [CommSemiring K]

open scoped Classical in
theorem denote_eq_sum_conditionEdge (N : Network K 0) (e : Fin N.shape.edges)
    (x : Fin 0 → Bool) :
    N.denote x = ∑ a : Bool, ∑ b : Bool,
      N.edge e a b * (N.conditionEdge e a b).denote x := by
  rw [← denote_asFinite, N.asFinite.denote_eq_sum_conditionEdge e x]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  apply Finset.sum_congr (by ext; simp)
  intro b _
  rw [conditionEdge, FiniteNetwork.denote_toNetwork]
  congr 2
  exact Subsingleton.elim _ _

theorem denote_eq_two_conditionEdge (N : Network K 0) (e : Fin N.shape.edges)
    (hX : N.edge e = Signature.disequality) (x : Fin 0 → Bool) :
    N.denote x = (N.conditionEdge e false true).denote x +
      (N.conditionEdge e true false).denote x := by
  classical
  rw [← denote_asFinite, N.asFinite.denote_eq_two_conditionEdge e hX x]
  simp only [conditionEdge, FiniteNetwork.denote_toNetwork]
  congr 2 <;> exact Subsingleton.elim _ _

theorem conditionEdge_oneHot (N : Network K 0) (e : Fin N.shape.edges)
    (a b : Bool) (hf : ∀ v, Signature.OneHot (N.vertex v))
    (v : Fin (N.conditionEdge e a b).shape.vertices) :
    Signature.OneHot ((N.conditionEdge e a b).vertex v) :=
  N.asFinite.conditionEdge_oneHot e a b hf ((Fintype.equivFin _).symm v)

theorem conditionEdge_native (N : Network K 0) (e : Fin N.shape.edges)
    (a b : Bool) (hX : ∀ d, N.edge d = Signature.disequality)
    (d : Fin (N.conditionEdge e a b).shape.edges) :
    (N.conditionEdge e a b).edge d = Signature.disequality :=
  hX ((Fintype.equivFin (FiniteNetwork.RemainingEdge e)).symm d).1

end Holant.Network
