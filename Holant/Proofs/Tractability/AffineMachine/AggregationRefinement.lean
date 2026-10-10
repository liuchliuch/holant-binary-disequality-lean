import Holant.Proofs.Tractability.AffineMachine.SparseRefinement
import Holant.Proofs.Tractability.AffineMachine.RawMachine
import Holant.Proofs.Tractability.ProductMachine.RawFamily


namespace Holant.LocalDrafts.Tractability.AffineMachine.AggregationRefinement

open Holant.Tractable AffinePhase TwoTranslate Holant.Complexity
open FixedGadgetSubstitution.Compiler ProductMachine EncodedTable
open SampleRefinement ReadRefinement
open scoped BigOperators

noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ} (D : Assembly.Family s b arity)

theorem collect_phase {n : ℕ} (as : List (State n)) (x : Word n) :
    (Assembly.collect as).phase.eval x = (as.map (fun A => A.phase.eval x)).sum := by
  induction as with
  | nil => simp [Assembly.collect, Assembly.unit, QuadraticPhase.eval, QuadraticPhase.zero]
  | cons A as ih => simp [Assembly.collect, Assembly.merge, Assembly.phaseAdd_eval, ih]

theorem collect_support {n : ℕ} (as : List (State n)) (x : Word n) :
    (Assembly.collect as).support.Holds x ↔ ∀ A ∈ as, A.support.Holds x := by
  induction as with
  | nil => simp [Assembly.collect, Assembly.unit]
  | cons A as ih => simp [Assembly.collect, Assembly.merge, AffineSystem.inter_holds, ih]

theorem vertex_address (r : Input s b arity) (v : Fin r.val.vertices.length)
    (j : Fin (arity (sourceLabel s b arity ⟨r, v⟩).val)) :
    Endpoint.number ((r.val.vertices.get v).2.getD j.val (0, false)) =
      (Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v, j⟩)).val := by
  rw [RawFamily.vertex_ports s b arity r v j]
  rfl

theorem vertex_word (r : Input s b arity) (v : Fin r.val.vertices.length)
    (x : Word (2 * r.val.edges.length)) :
    (fun j : Fin (arity (sourceLabel s b arity ⟨r, v⟩).val) =>
      (List.ofFn x).getD (Endpoint.number ((r.val.vertices.get v).2.getD j.val (0, false))) false) =
      (fun j => x (Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v, j⟩))) := by
  funext j
  rw [vertex_address, DensePrograms.getD_ofFn]

theorem edge_word (r : Input s b arity) (e : Fin r.val.edges.length)
    (x : Word (2 * r.val.edges.length)) :
    (fun j : Fin 2 => (List.ofFn x).getD
      (Endpoint.number ([(e.val, false), (e.val, true)].getD j.val (0, false))) false) =
      (fun j => x (Endpoint.typed r.val.edges.length (e, j == 1))) := by
  funext j
  fin_cases j
  · exact DensePrograms.getD_ofFn x (Endpoint.typed r.val.edges.length (e,false)) false
  · exact DensePrograms.getD_ofFn x (Endpoint.typed r.val.edges.length (e,true)) false

theorem vertex_sample (r : Input s b arity) (v : Fin r.val.vertices.length) (m : SamplePrograms.Mask) :
    SamplePrograms.phase m (RawBlocks.vertexBlock D ⟨r, v⟩).2.2 =
      (Assembly.vertexBlock D r v).phase.eval (assignment (2 * r.val.edges.length) m) := by
  rw [RawBlocks.vertexBlock, RawBlocks.block, SamplePrograms.phase_template]
  simp only [Assembly.vertexBlock, Assembly.place, Reconstruction.pullback_eval]
  congr 1
  funext j
  simp only [assignment, vertex_address]

theorem edge_sample (r : Input s b arity) (e : Fin r.val.edges.length) (m : SamplePrograms.Mask) :
    SamplePrograms.phase m (RawBlocks.edgeBlock D ⟨r, e⟩).2.2 =
      (Assembly.edgeBlock D r e).phase.eval (assignment (2 * r.val.edges.length) m) := by
  rw [RawBlocks.edgeBlock, RawBlocks.block, SamplePrograms.phase_template]
  simp only [Assembly.edgeBlock, Assembly.place, Reconstruction.pullback_eval]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem sample (r : Input s b arity) (m : SamplePrograms.Mask) :
    BlockAggregation.sample (2 * r.val.edges.length, RawBlocks.blocks D r) m =
      (Assembly.global D r).phase.eval (assignment (2 * r.val.edges.length) m) := by
  rw [Assembly.global, collect_phase]
  simp only [BlockAggregation.sample, BlockAggregation.phaseTerms, SamplePrograms.phase,
    RawBlocks.blocks, List.flatMap_append, List.map_append, List.sum_append,
    ListSums.flatMap_sum, List.map_map, Function.comp_def]
  change ((List.finRange r.val.vertices.length).map (fun v =>
    SamplePrograms.phase m (RawBlocks.vertexBlock D ⟨r, v⟩).2.2)).sum +
      ((List.finRange r.val.edges.length).map (fun e =>
        SamplePrograms.phase m (RawBlocks.edgeBlock D ⟨r, e⟩).2.2)).sum = _
  simp [vertex_sample, edge_sample, Assembly.blocks, List.ofFn_eq_map]

theorem phase_table (r : Input s b arity) :
    (RawMachine.initial D r).1.2.2 = sampled (Assembly.global D r).phase.eval := by
  simp only [RawMachine.initial, BlockAggregation.value, TabulatePhase.value, sampled, sample]

theorem regular (r : Input s b arity) : Regular (RawMachine.initial D r).1 := by
  have hr : ∀ row ∈ (RawMachine.initial D r).1.2.1,
      row.2.length = 2 * r.val.edges.length := by
    intro row h
    obtain ⟨raw, _, rfl⟩ := List.mem_map.mp h
    simp [BlockAggregation.row]
  have he : (RawMachine.initial D r).1 =
      (2 * r.val.edges.length, (RawMachine.initial D r).1.2.1,
        sampled (Assembly.global D r).phase.eval) := Prod.ext rfl (Prod.ext rfl (phase_table D r))
  rw [he]
  exact sampled_regular _ hr _ (quadratic_thirdDifference _)

theorem rows_holds {n : ℕ} (S : AffineSystem n) (ports : List RawEndpoint) (z : ℕ → Bool) :
    (∀ row ∈ RawBlocks.rows S ports, RawBlocks.rowHolds z row) ↔
      S.Holds (fun j => z (Endpoint.number (ports.getD j.val (0, false)))) := by
  simp [RawBlocks.rows, RawBlocks.row_exact, AffineSystem.Holds, TwoTranslate.dot]

theorem vertex_support (r : Input s b arity) (v : Fin r.val.vertices.length)
    (x : Word (2 * r.val.edges.length)) :
    (∀ row ∈ (RawBlocks.vertexBlock D ⟨r, v⟩).2.1,
      RawBlocks.rowHolds (fun k => (List.ofFn x).getD k false) row) ↔
        (Assembly.vertexBlock D r v).support.Holds x := by
  simp only [RawBlocks.vertexBlock, RawBlocks.block, rows_holds, vertex_word,
    Assembly.vertexBlock, Assembly.place, AffineSystem.pullback_holds, coordinates_isAffineMap]
  rfl

theorem edge_support (r : Input s b arity) (e : Fin r.val.edges.length)
    (x : Word (2 * r.val.edges.length)) :
    (∀ row ∈ (RawBlocks.edgeBlock D ⟨r, e⟩).2.1,
      RawBlocks.rowHolds (fun k => (List.ofFn x).getD k false) row) ↔
        (Assembly.edgeBlock D r e).support.Holds x := by
  simp only [RawBlocks.edgeBlock, RawBlocks.block, rows_holds, edge_word,
    Assembly.edgeBlock, Assembly.place, AffineSystem.pullback_holds, coordinates_isAffineMap]
  rfl

theorem support_holds (r : Input s b arity) (x : Word (2 * r.val.edges.length)) :
    (support (RawMachine.initial D r).1).Holds x ↔ (Assembly.global D r).support.Holds x := by
  dsimp only [RawMachine.initial]
  rw [SparseRefinement.support_holds, Assembly.global, collect_support]
  simp only [BlockAggregation.supportRows, RawBlocks.blocks, List.flatMap_append,
    List.forall_mem_append, List.forall_mem_flatMap, List.forall_mem_map, List.mem_finRange, forall_true_left,
    Assembly.blocks, List.forall_mem_ofFn_iff, vertex_support, edge_support]

theorem accumulator (r : Input s b arity) : (RawMachine.initial D r).2 = RawCode.accumulator r := by
  simp [RawMachine.initial, BlockAggregation.value, BlockAggregation.scaleCode, RawBlocks.blocks,
    RawBlocks.vertexBlock, RawBlocks.edgeBlock, RawBlocks.block, RawCode.accumulator, RawCode.labels,
    sourceLabel, RawCompiler.edgeLabel, List.ofFn_eq_map, List.map_map,
    Function.comp_def, RawClosedNetwork.signatureLabel]

def table (r : Input s b arity) := restore (RawMachine.initial D r).1 (regular D r)

theorem table_value (r : Input s b arity) (x : Word (2 * r.val.edges.length)) :
    ((table D r).state ((RawMachine.initial D r).2.eval (FamilyField.extra D))).value x =
      (Assembly.global D r).value x := by
  have hr : ∀ row ∈ (RawMachine.initial D r).1.2.1, row.2.length = 2 * r.val.edges.length :=
    (regular D r).1
  have he : (RawMachine.initial D r).1 =
      (2 * r.val.edges.length, (RawMachine.initial D r).1.2.1,
        sampled (Assembly.global D r).phase.eval) := Prod.ext rfl (Prod.ext rfl (phase_table D r))
  have hp : (phase (RawMachine.initial D r).1 (regular D r)).eval x =
      (Assembly.global D r).phase.eval x := by
    have hphase : phase (RawMachine.initial D r).1 (regular D r) =
        phase (2 * r.val.edges.length, (RawMachine.initial D r).1.2.1,
          sampled (Assembly.global D r).phase.eval)
          (sampled_regular _ hr _ (quadratic_thirdDifference _)) := by
      unfold phase constant linear mixed
      simp only [phase_table]
      rfl
    rw [hphase]
    exact sampled_eval _ hr _ (quadratic_thirdDifference _) x
  simp only [table, restore, Dense.Table.state, Dense.support_snapshot, Dense.phase_snapshot,
    State.value, affineFormula, accumulator, RawCode.accumulator_value, support_holds, hp]

end
end Holant.LocalDrafts.Tractability.AffineMachine.AggregationRefinement
