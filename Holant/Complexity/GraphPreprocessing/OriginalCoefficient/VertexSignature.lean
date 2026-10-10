import Holant.Complexity.GraphPreprocessing.ListIndex
import Holant.Complexity.GraphPreprocessing.Returning
import Holant.Complexity.ClosedNetworkEncoding

/-! Physical extraction of an original vertex's binary signature ID. The raw
network and unary original vertex query are preserved; copied edge/vertex/port
streams are cleared. No decoded graph, signature lookup or host index operation
is invoked by a transition. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexSignature
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false

abbrev Stack := Fin 4 ⊕ Fin 5
abbrev Label := Fin 7 ⊕ Fin 13
abbrev Statement := Stmt Stack Label Unit

def tapes (vertices index row scratch raw query temporary edges output : List Bool) : Stack → List Bool :=
  Sum.elim (ListIndex.tapes vertices index row scratch) ![raw, query, temporary, edges, output]

def config (label : Label) (vertices index row scratch raw query temporary edges output : List Bool) :=
  cfg label () (tapes vertices index row scratch raw query temporary edges output)

def returns (label : Fin 7) : Fin 13 := if label = 4 then 6 else 11

def controller (phase : Fin 13) : Statement :=
  match phase.val with
  | 0 => copyMoveStmt (.inr 0) (.inr 2) (.inr 0) (.inr 1)
  | 1 => copyRestoreStmt (.inr 0) (.inr 3) (.inr 2) (.inr 1) (.inr 2)
  | 2 => Frame.scanStmt (.inr 3) (.inl 3) (.inr 2) (.inr 3) (.inr 11)
  | 3 => copyMoveStmt (.inl 3) (.inl 0) (.inr 3) (.inr 4)
  | 4 => copyMoveStmt (.inr 1) (.inr 2) (.inr 4) (.inr 5)
  | 5 => copyRestoreStmt (.inr 1) (.inl 1) (.inr 2) (.inr 5) (.inl 0)
  | 6 => Frame.scanStmt (.inl 2) (.inl 3) (.inr 6) (.inr 7) (.inr 11)
  | 7 => copyMoveStmt (.inl 3) (.inr 4) (.inr 7) (.inr 8)
  | 8 => clearStmt (.inr 3) (.inr 8) (.inr 9)
  | 9 => clearStmt (.inl 0) (.inr 9) (.inr 10)
  | 10 => clearStmt (.inl 2) (.inr 10) (.inr 12)
  | _ => .halt

def program : Label → Statement := Returning.program ListIndex.machine.program returns controller

abbrev machine : BinaryCompose.Machine where
  K := Stack
  input := .inr 0
  output := .inr 4
  Label := Label
  main := .inr 0
  State := Option Bool × Unit
  initial := (none, ())
  program := program

/-- Success and rejection have distinct genuine terminal labels. -/
theorem success_halts (work : Stack → List Bool) :
    machine.computer.step (cfg (.inr 12 : Label) () work) =
      some (⟨none, (none, ()), work⟩ : Cfg Stack Label Unit) := rfl

theorem reject_halts (work : Stack → List Bool) :
    machine.computer.step (cfg (.inr 11 : Label) () work) =
      some (⟨none, (none, ()), work⟩ : Cfg Stack Label Unit) := rfl

/-- The original raw word is physically copied and restored before parsing. -/
theorem copy_raw (raw query output : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 0) [] [] [] [] raw query [] [] output)
      (config (.inr 2) [] [] [] [] raw query [] raw output) (2 * (raw.length + 1)) := by
  have h := copy_exact_frame (.inr 0 : Stack) (.inr 3) (.inr 2)
    (by decide) (by decide) (by decide) machine.computer.step (.inr 0) (.inr 1) (.inr 2)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (tapes [] [] [] [] [] query [] [] output) raw []
  convert h using 1 <;> dsimp [config, cfg] <;> congr 1 <;> funext key <;> cases key with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> simp [tapes3, tapes, Function.update]

/-- The raw outer vertex frame is parsed by real bit loops. -/
theorem extract_vertices (vertices edges raw query output : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 2) [] [] [] [] raw query [] (Holant.Algebraic.frame vertices ++ edges) output)
      (config (.inr 4) vertices [] [] [] raw query [] edges output) (2 * (vertices.length + 1)) := by
  have h := Frame.extract_exact (.inr 3 : Stack) (.inl 0) (.inl 3)
    (by decide) (by decide) (by decide) machine.computer.step (.inr 2) (.inr 3) (.inr 4) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (tapes [] [] [] [] raw query [] [] output) vertices edges []
  convert h using 1 <;> dsimp [config, cfg] <;> congr 1 <;> funext key <;> cases key with
  | inl k => fin_cases k <;> simp [tapes3, tapes, ListIndex.tapes, Function.update]
  | inr k => fin_cases k <;> rfl

/-- The caller's original unary vertex ID is preserved. -/
theorem copy_query (vertices edges raw query output : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 4) vertices [] [] [] raw query [] edges output)
      (config (.inl 0) vertices query [] [] raw query [] edges output) (2 * (query.length + 1)) := by
  have h := copy_exact_frame (.inr 1 : Stack) (.inl 1) (.inr 2)
    (by decide) (by decide) (by decide) machine.computer.step (.inr 4) (.inr 5) (.inl 0)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) ()
    (tapes vertices [] [] [] raw [] [] edges output) query []
  convert h using 1 <;> dsimp [config, cfg] <;> congr 1 <;> funext key <;> cases key with
  | inl k => fin_cases k <;> simp [tapes3, tapes, ListIndex.tapes, Function.update]
  | inr k => fin_cases k <;> simp [tapes3, tapes, Function.update]

/-- Exact original-order row access; only the unary prefix is consumed in the worker. -/
theorem index_vertex (pre tail : List RawVertex) (row : RawVertex)
    (raw query edges output : List Bool) :
    RunsExactly machine.computer.step
      (config (.inl 0) (framedListEncode RawClosedNetwork.vertexEncoding (pre ++ row :: tail))
        (List.replicate pre.length true) [] [] raw query [] edges output)
      (config (.inr 6) (framedListEncode RawClosedNetwork.vertexEncoding tail) []
        (RawClosedNetwork.vertexEncoding.encode row) [] raw query [] edges output)
      (ListIndex.ticks RawClosedNetwork.vertexEncoding pre row + 1) := by
  have h := ListIndex.index_exact RawClosedNetwork.vertexEncoding pre tail row [] []
  have active := Returning.run_active ListIndex.machine.program returns controller _ _
    ![raw, query, [], edges, output] _ h rfl
  change RunsExactly machine.computer.step _ _ _ at active
  simp only [List.append_nil] at active
  have ret := Returning.return_step ListIndex.machine.program returns controller (4 : Fin 7) rfl
    (none, ()) (ListIndex.tapes (framedListEncode RawClosedNetwork.vertexEncoding tail) []
      (RawClosedNetwork.vertexEncoding.encode row) []) ![raw, query, [], edges, output]
  change machine.computer.step _ = _ at ret
  have all := active.trans (runsExactly_one ret)
  simpa only [Returning.cfg, Option.map_some, List.append_nil, returns, reduceIte,
    config, cfg, tapes, program, Nat.add_comm] using all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.VertexSignature
