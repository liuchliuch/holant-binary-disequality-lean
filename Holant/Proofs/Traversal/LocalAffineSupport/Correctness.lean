import Holant.Proofs.Traversal.LocalAffineSupport.Matrix


namespace Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Correctness
open Holant Holant.Tractable AffinePhase TwoTranslate Holant.Complexity
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.Tractability.ProductMachine
open Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)

theorem vertex_port (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (v : Fin r.val.vertices.length) (j : Fin (arity (r.val.vertices.get v).1)) :
    (r.val.vertices.get v).2.getD j.val (0,false) = r.val.portEndpoint r.property ⟨v,j⟩ := by
  have hj : j.val < (r.val.vertices.get v).2.length := by
    rw [(r.property.1 v).2]
    exact j.isLt
  rw [List.getD_eq_getElem _ _ hj]
  rfl

theorem vertex_address (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (v : Fin r.val.vertices.length) (j : Fin (arity (r.val.vertices.get v).1)) :
    Endpoint.number ((r.val.vertices.get v).2.getD j.val (0,false)) =
      (Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v,j⟩)).val := by
  rw [vertex_port]
  rfl

theorem vertex_address_bound (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (v : Fin r.val.vertices.length) (j : Fin (arity (r.val.vertices.get v).1)) :
    Endpoint.number ((r.val.vertices.get v).2.getD j.val (0,false)) < 2*r.val.edges.length := by
  rw [vertex_address]
  exact (Endpoint.typed _ _).isLt

theorem vertex_word (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (v : Fin r.val.vertices.length) (x : Word (2*r.val.edges.length)) :
    (fun j : Fin (arity (r.val.vertices.get v).1) => (List.ofFn x).getD
      (Endpoint.number ((r.val.vertices.get v).2.getD j.val (0,false))) false) =
      (LocalAffineLabels.network D r).shape.assignment Fin.elim0
        (Holant.LocalDrafts.MainChain.LocalAffineSupport.assignment r.val.edges.length x) v := by
  funext j
  rw [vertex_address, DensePrograms.getD_ofFn]
  rfl

theorem edge_word (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (e : Fin r.val.edges.length) (x : Word (2*r.val.edges.length)) :
    (fun j : Fin 2 => (List.ofFn x).getD
      (Endpoint.number ([(e.val,false),(e.val,true)].getD j.val (0,false))) false) =
      ![x (Endpoint.typed r.val.edges.length (e,false)),
        x (Endpoint.typed r.val.edges.length (e,true))] := by
  funext j
  fin_cases j
  · exact DensePrograms.getD_ofFn x (Endpoint.typed r.val.edges.length (e,false)) false
  · exact DensePrograms.getD_ofFn x (Endpoint.typed r.val.edges.length (e,true)) false

theorem rows_holds {n : ℕ} (S : AffineSystem n) (ports : List RawEndpoint) (z : ℕ → Bool) :
    (∀ row ∈ RawBlocks.rows S ports, RawBlocks.rowHolds z row) ↔
      S.Holds (fun j => z (Endpoint.number (ports.getD j.val (0,false)))) := by
  simp [RawBlocks.rows, RawBlocks.row_exact, AffineSystem.Holds, TwoTranslate.dot]

theorem vertex_holds (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (v : Fin r.val.vertices.length) (x : Word (2*r.val.edges.length)) :
    (∀ row ∈ RawRows.vertex D ⟨r,v⟩, RawBlocks.rowHolds (fun k => (List.ofFn x).getD k false) row) ↔
      (LocalAffineLabels.network D r).vertex v
        ((LocalAffineLabels.network D r).shape.assignment Fin.elim0
          (Holant.LocalDrafts.MainChain.LocalAffineSupport.assignment r.val.edges.length x) v) ≠ 0 := by
  rw [RawRows.vertex, rows_holds]
  dsimp only [sourceLabel, LocalAffineLabels.network, RawClosedNetwork.realize]
  erw [vertex_word D r v x]
  rw [LocalData.vertex_holds]
  rfl

theorem edge_holds (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (e : Fin r.val.edges.length) (x : Word (2*r.val.edges.length)) :
    (∀ row ∈ RawRows.edge D ⟨r,e⟩, RawBlocks.rowHolds (fun k => (List.ofFn x).getD k false) row) ↔
      (LocalAffineLabels.network D r).edge e
        (x (Endpoint.typed r.val.edges.length (e,false)))
        (x (Endpoint.typed r.val.edges.length (e,true))) ≠ 0 := by
  rw [RawRows.edge, rows_holds, edge_word, LocalData.edge_holds]
  rfl

private theorem all_flatMap {A B : Type} (xs : List A) (f : A → List B) (P : B → Prop) :
    (∀ y ∈ xs.flatMap f, P y) ↔ ∀ a ∈ xs, ∀ y ∈ f a, P y := by
  constructor
  · intro h a ha y hy
    exact h y (List.mem_flatMap.mpr ⟨a,ha,hy⟩)
  · intro h y hy
    obtain ⟨a,ha,hy⟩ := List.mem_flatMap.mp hy
    exact h a ha y hy

/-- Actual emitted support, with no supplied incidence or support certificate. -/
theorem support_iff (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (x : Word (2*r.val.edges.length)) :
    (Codec.support (Matrix.value D r)).Holds x ↔
      (LocalAffineLabels.network D r).assignmentTerm Fin.elim0
        (Holant.LocalDrafts.MainChain.LocalAffineSupport.assignment r.val.edges.length x) ≠ 0 := by
  change (Codec.support (Matrix.materialize _ (RawRows.value D r))).Holds x ↔ _
  rw [Matrix.holds_materialize]
  simp only [RawRows.value, List.forall_mem_append, all_flatMap]
  simp only [List.mem_finRange, forall_true_left, vertex_holds, edge_holds]
  simp [Network.assignmentTerm, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Holant.LocalDrafts.MainChain.LocalAffineSupport.assignment]
  rfl

set_option maxHeartbeats 800000 in
/-- The explicit zero row convention may differ from a chosen localSystem's
row syntax. Both systems have exactly the same Holds predicate. -/
theorem same_holds_global (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (x : Word (2*r.val.edges.length)) :
    (Codec.support (Matrix.value D r)).Holds x ↔
      (Holant.LocalDrafts.MainChain.LocalAffineSupport.global (LocalAffineLabels.network D r)
        (fun v => D.vertexLocal (r.val.signatureLabel r.property v))
        (fun e => D.edgeLocal (r.val.edgeLabel r.property e))).Holds x :=
  (support_iff D r x).trans
    (Holant.LocalDrafts.MainChain.LocalAffineSupport.global_holds (LocalAffineLabels.network D r)
      (fun v => D.vertexLocal (r.val.signatureLabel r.property v))
      (fun e => D.edgeLocal (r.val.edgeLabel r.property e)) x).symm

end
end Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Correctness
