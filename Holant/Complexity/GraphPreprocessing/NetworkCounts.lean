import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Complexity.GraphPreprocessing.ListScan
import Holant.Complexity.GraphPreprocessing.Primitive
import Holant.Complexity.ClosedNetworkEncoding

/-!
# Linear bit-machine preparation of graph size counters

This actual finite Boolean-stack machine starts on the exact raw/validated
closed-network input codec. It preserves the entire original input by a proved
bitwise copy, separates the outer frame, traverses both actual framed lists, and
allocates one Boolean bit for each original vertex and edge. No ID is converted
to a magnitude-dependent loop bound. This is a front-end stage, not a claim that
validation, endpoint inversion, reachability or parent tables have been compiled.
-/
namespace Holant.Complexity.GraphPreprocessing.NetworkCounts
open Turing StackProtocol Computability

abbrev machine : BinaryCompose.Machine where
  K := Fin 7
  input := 0
  output := 5
  Label := Fin 10
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label = 0 then copyMoveStmt 0 2 0 1
    else if label = 1 then copyRestoreStmt 0 1 2 1 2
    else if label = 2 then Frame.scanStmt 1 4 2 3 9
    else if label = 3 then copyMoveStmt 4 3 3 4
    else if label = 4 then ListScan.markerStmt 3 5 4 5 6 9
    else if label = 5 then ListScan.skipStmt 3 5 4 9
    else if label = 6 then ListScan.markerStmt 1 6 6 7 8 9
    else if label = 7 then ListScan.skipStmt 1 7 6 9
    else .halt

def tapes (original work copyTmp vertices parseTmp vertexCount edgeCount : List Bool) : Fin 7 → List Bool :=
  ![original, work, copyTmp, vertices, parseTmp, vertexCount, edgeCount]

private theorem copy_move_exec : ExecutesAt machine.computer.step (0 : Fin 10) (copyMoveStmt 0 2 0 1) := by
  intro state tapes; rfl
private theorem copy_restore_exec : ExecutesAt machine.computer.step (1 : Fin 10) (copyRestoreStmt 0 1 2 1 2) := by
  intro state tapes; rfl
private theorem scan_exec : ExecutesAt machine.computer.step (2 : Fin 10) (Frame.scanStmt 1 4 2 3 9) := by
  intro state tapes; rfl
private theorem restore_exec : ExecutesAt machine.computer.step (3 : Fin 10) (copyMoveStmt 4 3 3 4) := by
  intro state tapes; rfl
private theorem vertices_marker_exec : ExecutesAt machine.computer.step (4 : Fin 10) (ListScan.markerStmt 3 5 4 5 6 9) := by
  intro state tapes; rfl
private theorem vertices_skip_exec : ExecutesAt machine.computer.step (5 : Fin 10) (ListScan.skipStmt 3 5 4 9) := by
  intro state tapes; rfl
private theorem edges_marker_exec : ExecutesAt machine.computer.step (6 : Fin 10) (ListScan.markerStmt 1 6 6 7 8 9) := by
  intro state tapes; rfl
private theorem edges_skip_exec : ExecutesAt machine.computer.step (7 : Fin 10) (ListScan.skipStmt 1 7 6 9) := by
  intro state tapes; rfl

theorem copy_input (input : List Bool) :
    RunsExactly machine.computer.step (cfg (0 : Fin 10) () (tapes input [] [] [] [] [] []))
      (cfg (2 : Fin 10) () (tapes input input [] [] [] [] [])) (2 * (input.length + 1)) := by
  have h := copy_exact (0 : Fin 7) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step 0 1 2 copy_move_exec copy_restore_exec () (tapes input [] [] [] [] [] []) rfl
  change RunsExactly _ _ (cfg _ _ (Function.update _ 1 (input ++ []))) _ at h
  simp only [List.append_nil] at h
  convert h using 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · rfl

theorem split_outer (original vertices edges : List Bool) :
    RunsExactly machine.computer.step
      (cfg (2 : Fin 10) () (tapes original (Holant.Algebraic.frame vertices ++ edges) [] [] [] [] []))
      (cfg (4 : Fin 10) () (tapes original edges [] vertices [] [] [])) (2 * (vertices.length + 1)) := by
  have h := Frame.extract_exact (1 : Fin 7) 3 4 (by decide) (by decide) (by decide)
    machine.computer.step 2 3 4 9 scan_exec restore_exec ()
      (tapes original [] [] [] [] [] []) vertices edges []
  simp only [List.append_nil] at h
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem count_vertices (original edges : List Bool) (vertices : List RawVertex) :
    RunsExactly machine.computer.step
      (cfg (4 : Fin 10) () (tapes original edges [] (framedListEncode RawClosedNetwork.vertexEncoding vertices) [] [] []))
      (cfg (6 : Fin 10) () (tapes original edges [] [] [] (List.replicate vertices.length true) []))
      (ListScan.ticks RawClosedNetwork.vertexEncoding vertices) := by
  have h := ListScan.count_exact (3 : Fin 7) 5 (by decide) machine.computer.step 4 5 6 9
    vertices_marker_exec vertices_skip_exec RawClosedNetwork.vertexEncoding ()
      (tapes original edges [] [] [] [] []) vertices [] []
  simp only [List.append_nil] at h
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem count_edges (original vertexCount : List Bool) (edges : List ℕ) :
    RunsExactly machine.computer.step
      (cfg (6 : Fin 10) () (tapes original (framedListEncode encodingNatBool edges) [] [] [] vertexCount []))
      (cfg (8 : Fin 10) () (tapes original [] [] [] [] vertexCount (List.replicate edges.length true)))
      (ListScan.ticks encodingNatBool edges) := by
  have h := ListScan.count_exact (1 : Fin 7) 6 (by decide) machine.computer.step 6 7 8 9
    edges_marker_exec edges_skip_exec encodingNatBool ()
      (tapes original [] [] [] [] vertexCount []) edges [] []
  simp only [List.append_nil] at h
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

def transitionCount (r : RawClosedNetwork) : ℕ :=
  2 * ((RawClosedNetwork.encoding.encode r).length + 1) +
  2 * ((framedListEncode RawClosedNetwork.vertexEncoding r.vertices).length + 1) +
  ListScan.ticks RawClosedNetwork.vertexEncoding r.vertices + ListScan.ticks encodingNatBool r.edges

def result (r : RawClosedNetwork) : machine.Config :=
  cfg (8 : Fin 10) () (tapes (RawClosedNetwork.encoding.encode r) [] [] [] []
    (List.replicate r.vertices.length true) (List.replicate r.edges.length true))

theorem initial_eq (input : List Bool) :
    cfg (0 : Fin 10) () (tapes input [] [] [] [] [] []) = initList machine.computer input := by
  rw [BinaryCompose.Machine.init_eq]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Operational preparation from the actual encoded network, preserving that input. -/
theorem prepare_exact (r : RawClosedNetwork) :
    RunsExactly machine.computer.step (initList machine.computer (RawClosedNetwork.encoding.encode r))
      (result r) (transitionCount r) := by
  have first := copy_input (RawClosedNetwork.encoding.encode r)
  rw [initial_eq] at first
  have second := split_outer (RawClosedNetwork.encoding.encode r)
    (framedListEncode RawClosedNetwork.vertexEncoding r.vertices) (framedListEncode encodingNatBool r.edges)
  have third := count_vertices (RawClosedNetwork.encoding.encode r) (framedListEncode encodingNatBool r.edges) r.vertices
  have fourth := count_edges (RawClosedNetwork.encoding.encode r) (List.replicate r.vertices.length true) r.edges
  have run := ((first.trans second).trans third).trans fourth
  convert run using 1
  · rfl
  · unfold transitionCount
    omega

/-- Parsing, copies, marker tests, allocation and empty-stack tests are included. -/
theorem transitionCount_le (r : RawClosedNetwork) :
    transitionCount r ≤ 4 * (RawClosedNetwork.encoding.encode r).length + 4 := by
  have hv := ListScan.ticks_le_length RawClosedNetwork.vertexEncoding r.vertices
  have he := ListScan.ticks_le_length encodingNatBool r.edges
  have hl : (RawClosedNetwork.encoding.encode r).length =
      2 * (framedListEncode RawClosedNetwork.vertexEncoding r.vertices).length + 1 +
      (framedListEncode encodingNatBool r.edges).length := by
    exact framedProductEncoding_length (framedListEncoding RawClosedNetwork.vertexEncoding)
      (framedListEncoding encodingNatBool) (r.vertices, r.edges)
  unfold transitionCount
  omega

def prepare_correct (r : RawClosedNetwork) :
    StateTransition.EvalsToInTime machine.computer.step
      (initList machine.computer (RawClosedNetwork.encoding.encode r)) (some (result r))
      (4 * (RawClosedNetwork.encoding.encode r).length + 4) where
  steps := transitionCount r
  evals_in_steps := prepare_exact r
  steps_le_m := transitionCount_le r

theorem program_budget (label : Fin 10) : TM2Cost.budget (machine.program label) ≤ 8 := by
  fin_cases label <;> decide

/-- This counts the actual executed elementary Boolean-stack instructions. -/
theorem prepare_bit_cost (r : RawClosedNetwork) :
    (Primitive.run machine.program (transitionCount r)
      (some (initList machine.computer (RawClosedNetwork.encoding.encode r)))).2 = some (result r) ∧
    (Primitive.run machine.program (transitionCount r)
      (some (initList machine.computer (RawClosedNetwork.encoding.encode r)))).1 ≤
      32 * (RawClosedNetwork.encoding.encode r).length + 32 := by
  have h := Primitive.execution_cost machine.program 8 program_budget (transitionCount r)
    (initList machine.computer (RawClosedNetwork.encoding.encode r)) (result r) (prepare_exact r)
  refine ⟨h.1, le_trans h.2 ?_⟩
  have ht := transitionCount_le r
  omega

/-- The exact same machine accepts the genuine validated-encoding input convention. -/
theorem prepare_validated {s b : ℕ} {arity : ℕ → ℕ}
    (r : {r : RawClosedNetwork // r.WellFormed s b arity}) :
    RunsExactly machine.computer.step
      (initList machine.computer ((RawClosedNetwork.validatedEncoding s b arity).encode r))
      (result r.val) (transitionCount r.val) := prepare_exact r.val

@[simp] theorem result_original (r : RawClosedNetwork) :
    (result r).stk 0 = RawClosedNetwork.encoding.encode r := rfl
@[simp] theorem result_vertex_count (r : RawClosedNetwork) :
    ((result r).stk 5).length = r.vertices.length := by simp [result, tapes, cfg]
@[simp] theorem result_edge_count (r : RawClosedNetwork) :
    ((result r).stk 6).length = r.edges.length := by simp [result, tapes, cfg]

end Holant.Complexity.GraphPreprocessing.NetworkCounts
