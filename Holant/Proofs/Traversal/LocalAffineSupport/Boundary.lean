import Holant.Proofs.Traversal.LocalAffineSupport.Correctness


namespace Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Boundary
open Holant Holant.Tractable AffinePhase TwoTranslate Holant.Complexity
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine
noncomputable section

theorem impossible_rows (n : ℕ) (ports : List RawEndpoint) :
    RawBlocks.rows (Holant.LocalDrafts.MainChain.LocalAffineSupport.impossible n) ports = [(true,[])] := by
  simp [RawBlocks.rows, RawBlocks.row, RawBlocks.columns,
    Holant.LocalDrafts.MainChain.LocalAffineSupport.impossible, residueBit]

theorem dense_impossible (n : ℕ) : BlockAggregation.row n (true,[]) =
    (true,List.replicate n false) := by
  simp [BlockAggregation.row, SamplePrograms.parity, ResidueCells.parity]

theorem impossible_holds (n : ℕ) (x : Word n) :
    ¬ (Codec.support (Matrix.materialize n [(true,[])])).Holds x := by
  rw [Matrix.holds_materialize]
  simp [RawBlocks.rowHolds]

variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)

theorem zero_vertex (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (v : Fin r.val.vertices.length)
    (hz : D.signatures (r.val.signatureLabel r.property v) = 0) :
    RawRows.vertex D ⟨r,v⟩ = [(true,[])] := by
  unfold RawRows.vertex LocalData.vertex
  change RawBlocks.rows (LocalData.system _ _) _ = _
  have hz' : D.signatures (sourceLabel s b arity ⟨r,v⟩) = 0 := hz
  rw [LocalData.system_zero _ _ hz']
  exact impossible_rows _ _

theorem zero_edge (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (e : Fin r.val.edges.length)
    (hz : kernelSignature (D.kernels (r.val.edgeLabel r.property e)) = 0) :
    RawRows.edge D ⟨r,e⟩ = [(true,[])] := by
  unfold RawRows.edge LocalData.edge
  change RawBlocks.rows (LocalData.system _ _) _ = _
  have hz' : kernelSignature (D.kernels (Holant.LocalDrafts.Tractability.ProductMachine.RawCompiler.edgeLabel s b arity ⟨r,e⟩)) = 0 := hz
  rw [LocalData.system_zero _ _ hz']
  exact impossible_rows _ _

/-- Membership is in the actual emitted row list, not in a proposed witness. -/
theorem zero_vertex_emitted (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (v : Fin r.val.vertices.length)
    (hz : D.signatures (r.val.signatureLabel r.property v) = 0) :
    (true,List.replicate (2*r.val.edges.length) false) ∈ (Matrix.value D r).2 := by
  apply List.mem_map.mpr
  refine ⟨(true,[]), ?_, dense_impossible _⟩
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨v, by simp, ?_⟩
  rw [zero_vertex D r v hz]
  simp

theorem zero_edge_emitted (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (e : Fin r.val.edges.length)
    (hz : kernelSignature (D.kernels (r.val.edgeLabel r.property e)) = 0) :
    (true,List.replicate (2*r.val.edges.length) false) ∈ (Matrix.value D r).2 := by
  apply List.mem_map.mpr
  refine ⟨(true,[]), ?_, dense_impossible _⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨e, by simp, ?_⟩
  rw [zero_edge D r e hz]
  simp

theorem nullary_ports (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (v : Fin r.val.vertices.length) (hn : arity (r.val.vertices.get v).1 = 0) :
    (r.val.vertices.get v).2 = [] := by
  apply List.eq_nil_of_length_eq_zero
  exact ((r.property.1 v).2).trans hn

/-- Without edges every actual vertex is nullary: validity rules out a free
unary stub. Such vertices are nevertheless included by the all-vertex loop. -/
theorem zero_edges_nullary (r : RawRows.Input (s:=s) (b:=b) (arity:=arity))
    (he : r.val.edges.length = 0) (v : Fin r.val.vertices.length) :
    arity (r.val.vertices.get v).1 = 0 := by
  by_contra hn
  let j : Fin (arity (r.val.vertices.get v).1) := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hb := r.val.portEndpoint_bound r.property ⟨v,j⟩
  omega

end
end Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Boundary
