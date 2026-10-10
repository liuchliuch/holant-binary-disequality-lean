import Holant.Proofs.Traversal.ArityTwo.OrderedDenote


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
open Holant Holant.Complexity PortWalk
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

noncomputable def rootComponentEquiv : {v // v ∈ (r.graph h).roots} ≃ (r.shape h).Component :=
  Equiv.ofBijective (fun v => (r.shape h).componentOf v.val) (by
    constructor
    · intro u v huv
      apply Subtype.ext
      have hl := (r.graph_label_eq_iff h u.val v.val).mpr huv
      simpa only [((r.graph h).mem_roots u.val).mp u.property,
        ((r.graph h).mem_roots v.val).mp v.property] using hl
    · intro c
      obtain ⟨v,rfl⟩ := (r.shape h).componentOf_surjective c
      refine ⟨⟨(r.graph h).label v,(r.graph h).label_mem_roots v⟩,?_⟩
      exact (r.graph_label_eq_iff h _ v).mp ((r.graph h).label_idempotent v))

noncomputable def rootOrderEquiv : Fin (r.graph h).roots.length ≃ (r.shape h).Component :=
  (listFiberEquiv (r.graph h).roots (r.graph h).roots_nodup
    (fun v => v ∈ (r.graph h).roots) (fun _ => Iff.rfl)).trans (rootComponentEquiv r h)

theorem nullary_label_iff (root : Fin r.vertices.length) (hz : degree (arity := arity) r root = 0)
    (v : Fin r.vertices.length) :
    (r.graph h).label v = (r.graph h).label root ↔ v = root := by
  have hn (e : (r.graph h).Edge) (z : Bool) : (r.graph h).endpoint e z ≠ root := by
    rw [endpoint_lookup]
    exact nullary_no_port r root hz _
  constructor
  · intro hl
    have hr := ((r.graph h).label_eq_iff v root).mp hl
    have invariant {u v : Fin r.vertices.length}
        (hr : Relation.EqvGen (Holant.OneHot.Decomposition.Link (r.graph h).endpoint) u v) :
        u = root ↔ v = root := by
      induction hr with
      | rel u v hr =>
        obtain ⟨e,rfl,rfl⟩ := hr
        exact iff_of_false (hn e false) (hn e true)
      | refl u => rfl
      | symm u v hr ih => exact ih.symm
      | trans u v w hr hs ih₁ ih₂ => exact ih₁.trans ih₂
    exact (invariant hr).mpr rfl
  · rintro rfl
    rfl

variable {K : Type*} [CommSemiring K]
variable (signatures : (i : Fin s) → Signature K (arity i.val)) (kernels : Fin b → Kernel K)

/-- The product index is the list emitted by the existing RawRoots machine. -/
theorem raw_denote_roots :
    (r.realize h signatures kernels).denote Fin.elim0 =
      ∏ i : Fin (r.graph h).roots.length,
        ((r.realize h signatures kernels).componentFiniteNetwork
          ((r.shape h).componentOf ((r.graph h).roots.get i))).denote Fin.elim0 := by
  classical
  rw [Network.denote_eq_prod_componentFiniteNetwork]
  exact ((rootOrderEquiv r h).prod_comp
    (fun c => ((r.realize h signatures kernels).componentFiniteNetwork c).denote Fin.elim0)).symm

theorem nullary_component_denote (root : Fin r.vertices.length) (hz : degree (arity := arity) r root = 0) :
    ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h root)).denote Fin.elim0 =
      signatures (r.signatureLabel h root) (fun _ => false) := by
  classical
  letI : Unique ((r.shape h).ComponentVertex (Comp r h root)) := {
    default := ⟨root,rfl⟩
    uniq v := Subtype.ext ((nullary_label_iff r h root hz v.val).mp
      ((r.graph_label_eq_iff h v.val root).mpr v.property)) }
  letI : IsEmpty ((r.shape h).ComponentEdge (Comp r h root)) := ⟨by
    intro e
    have he : (r.graph h).label (r.lookup h (e.val,false)).1 = (r.graph h).label root := by
      apply (r.graph_label_eq_iff h _ root).mpr
      rw [r.lookup_vertex h]
      exact e.property
    exact nullary_no_port r root hz (r.lookup h (e.val,false))
      ((nullary_label_iff r h root hz _).mp he)⟩
  rw [Network.denote_componentFiniteNetwork]
  have harg (z : ((r.shape h).ComponentEdge (Comp r h root) × Bool) → Bool) :
      (fun j => z ((r.shape h).componentClosedPorts (Comp r h root) ⟨⟨root,rfl⟩,j⟩)) =
        (fun _ => false) := by
    funext j
    have hj := j.isLt
    change j.val < degree (arity := arity) r root at hj
    omega
  simp [Network.componentTerm,RawClosedNetwork.realize,harg]
  change signatures (r.signatureLabel h root) _ = _
  congr 1
  exact harg _

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
