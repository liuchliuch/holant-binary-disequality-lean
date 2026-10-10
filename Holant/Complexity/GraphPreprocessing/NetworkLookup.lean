import Holant.Complexity.GraphPreprocessing.Returning
import Holant.Complexity.GraphPreprocessing.PortSearch
import Holant.Complexity.GraphPreprocessing.ListScan

/-!
# Nested search through the actual raw closed-network serialization

This finite Boolean-stack program opens the actual outer frame, walks original
vertex records, skips each framed signature label bitwise, and invokes the proved
literal port-search machine. Its separate found/missing/error returns are really
compiled. Both original vertex and local port positions are physical unary
stacks; no decoded natural controls iteration or allocation.
-/
namespace Holant.Complexity.GraphPreprocessing.NetworkLookup
open Turing Computability StackProtocol RawClosedNetwork
open Turing.TM2.Stmt
abbrev Stack := Fin 7 ⊕ Fin 4
abbrev Label := Fin 10 ⊕ Fin 11
abbrev Statement := Stmt Stack Label FramedFind.Caller

/-- Source exits 6/8/9 return to found/next-vertex/error respectively. -/
def returns (label : Fin 10) : Fin 11 := if label = 6 then 8 else if label = 8 then 6 else 10

def vertexMarker : Statement :=
  pop (.inr 1) (fun v bit => (bit, v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun v => (none, v.2)) (goto (fun _ => .inr 3)))
        (load (fun v => (none, v.2)) (goto (fun _ => .inr 9))))
      (load (fun v => (none, v.2)) (goto (fun _ => .inr 10))))

def outside (phase : Fin 11) : Statement :=
  if phase = 0 then Frame.scanStmt (.inr 0) (.inr 2) (.inr 0) (.inr 1) (.inr 10)
  else if phase = 1 then copyMoveStmt (.inr 2) (.inr 1) (.inr 1) (.inr 2)
  else if phase = 2 then vertexMarker
  else if phase = 3 then Frame.scanStmt (.inr 1) (.inr 2) (.inr 3) (.inr 4) (.inr 10)
  else if phase = 4 then copyMoveStmt (.inr 2) (.inl 0) (.inr 4) (.inr 5)
  else if phase = 5 then ListScan.skipStmt (.inl 0) (.inr 5) (.inl 0) (.inr 10)
  else if phase = 6 then clearStmt (.inl 6) (.inr 6) (.inr 7)
  else if phase = 7 then push (.inr 3) (fun _ => true) (goto (fun _ => .inr 2))
  else .halt

abbrev machine : BinaryCompose.Machine where
  K := Stack
  input := .inr 0
  output := .inr 3
  Label := Label
  main := .inr 0
  State := WordEqual.Memory Unit
  initial := WordEqual.clean true ()
  program := Returning.program FramedFind.machine.program returns outside

def extras (input vertices scratch vertexCount : List Bool) : Fin 4 → List Bool :=
  ![input, vertices, scratch, vertexCount]

def tapes (source query portCount input vertices scratch vertexCount : List Bool) : Stack → List Bool :=
  Sum.elim (FramedFind.tapes source query [] [] [] [] portCount) (extras input vertices scratch vertexCount)

def config (label : Label) (source query portCount input vertices scratch vertexCount : List Bool) : machine.Config :=
  WordEqual.cfg label true () (tapes source query portCount input vertices scratch vertexCount)

private theorem at_outer : ExecutesAt machine.computer.step (.inr (0 : Fin 11))
    (Frame.scanStmt (.inr 0) (.inr 2) (.inr 0) (.inr 1) (.inr 10)) := by intro state tapes; rfl
private theorem at_outer_restore : ExecutesAt machine.computer.step (.inr (1 : Fin 11))
    (copyMoveStmt (.inr 2) (.inr 1) (.inr 1) (.inr 2)) := by intro state tapes; rfl
private theorem at_vertex_scan : ExecutesAt machine.computer.step (.inr (3 : Fin 11))
    (Frame.scanStmt (.inr 1) (.inr 2) (.inr 3) (.inr 4) (.inr 10)) := by intro state tapes; rfl
private theorem at_vertex_restore : ExecutesAt machine.computer.step (.inr (4 : Fin 11))
    (copyMoveStmt (.inr 2) (.inl 0) (.inr 4) (.inr 5)) := by intro state tapes; rfl
private theorem at_signature : ExecutesAt machine.computer.step (.inr (5 : Fin 11))
    (ListScan.skipStmt (.inl 0) (.inr 5) (.inl 0) (.inr 10)) := by intro state tapes; rfl
private theorem at_clear : ExecutesAt machine.computer.step (.inr (6 : Fin 11))
    (clearStmt (.inl 6) (.inr 6) (.inr 7)) := by intro state tapes; rfl

theorem outer_exact (vertices edges query : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 0) [] query [] (Holant.Algebraic.frame vertices ++ edges) [] [] [])
      (config (.inr 2) [] query [] edges vertices [] []) (2 * (vertices.length + 1)) := by
  have h := Frame.extract_exact (.inr (0 : Fin 4) : Stack) (.inr 1) (.inr 2)
    (by decide) (by decide) (by decide) machine.computer.step (.inr 0) (.inr 1) (.inr 2) (.inr 10)
    at_outer at_outer_restore (true, none, ()) (tapes [] query [] [] [] [] []) vertices edges []
  simp only [List.append_nil] at h
  convert h using 1 <;> unfold config WordEqual.cfg cfg WordEqual.clean <;> congr 1 <;> funext k
  all_goals cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl

theorem marker_entry (vertices query edges vertexCount : List Bool) :
    machine.computer.step (config (.inr 2) [] query [] edges (true :: vertices) [] vertexCount) =
      some (config (.inr 3) [] query [] edges vertices [] vertexCount) := by
  have hs : ExecutesAt machine.computer.step (.inr (2 : Fin 11)) vertexMarker := by intro state tapes; rfl
  rw [config, WordEqual.cfg, hs]
  simp [vertexMarker, config, WordEqual.cfg, WordEqual.clean, TM2.stepAux, tapes, extras,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem vertex_extract (word vertices query edges vertexCount : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 3) [] query [] edges (Holant.Algebraic.frame word ++ vertices) [] vertexCount)
      (config (.inr 5) word query [] edges vertices [] vertexCount) (2 * (word.length + 1)) := by
  have h := Frame.extract_exact (.inr (1 : Fin 4) : Stack) (.inl 0) (.inr 2)
    (by decide) (by decide) (by decide) machine.computer.step (.inr 3) (.inr 4) (.inr 5) (.inr 10)
    at_vertex_scan at_vertex_restore (true, none, ()) (tapes [] query [] edges [] [] vertexCount) word vertices []
  simp only [List.append_nil] at h
  convert h using 1 <;> unfold config WordEqual.cfg cfg WordEqual.clean <;> congr 1 <;> funext k
  all_goals cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl

theorem signature_skip (label : ℕ) (ports vertices query edges vertexCount : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 5) (Holant.Algebraic.frame (encodeNat label) ++ ports) query [] edges vertices [] vertexCount)
      (config (.inl 0) ports query [] edges vertices [] vertexCount) ((encodeNat label).length + 1) := by
  have h := ListScan.skip_exact (.inl (0 : Fin 7) : Stack) (.inl 6) (by decide)
    machine.computer.step (.inr 5) (.inl 0) (.inr 10) at_signature (true, none, ())
    (tapes [] query [] edges vertices [] vertexCount) (encodeNat label) ports []
  convert h using 1 <;> unfold config WordEqual.cfg cfg WordEqual.clean <;> congr 1 <;> funext k
  all_goals cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl

def prepareTicks (row : RawVertex) : ℕ := 2 * (vertexEncoding.encode row).length + (encodeNat row.1).length + 4

/-- Parse one original vertex and reach the real embedded port-search entry. -/
theorem prepare_vertex (row : RawVertex) (vertices query edges vertexCount : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 2) [] query [] edges (true :: (Holant.Algebraic.frame (vertexEncoding.encode row) ++ vertices)) [] vertexCount)
      (config (.inl 0) (framedListEncode endpointEncoding row.2) query [] edges vertices [] vertexCount)
      (prepareTicks row) := by
  have h := ((runsExactly_one (marker_entry (Holant.Algebraic.frame (vertexEncoding.encode row) ++ vertices) query edges vertexCount)).trans
    (vertex_extract (vertexEncoding.encode row) vertices query edges vertexCount)).trans
    (signature_skip row.1 (framedListEncode endpointEncoding row.2) vertices query edges vertexCount)
  convert h using 1
  unfold prepareTicks
  omega

/-- Every active execution of the source search block is retained with its exact cost. -/
theorem lift_search (c d : FramedFind.machine.Config) (n : ℕ)
    (h : RunsExactly FramedFind.machine.computer.step c d n) (active : d.l.isSome)
    (edges vertices vertexCount : List Bool) :
    RunsExactly machine.computer.step
      (Returning.cfg c (extras edges vertices [] vertexCount))
      (Returning.cfg d (extras edges vertices [] vertexCount)) n :=
  Returning.run_active FramedFind.machine.program returns outside c d _ n h active

theorem return_found (source query portCount edges vertices vertexCount : List Bool) :
    machine.computer.step (config (.inl 6) source query portCount edges vertices [] vertexCount) =
      some (config (.inr 8) source query portCount edges vertices [] vertexCount) := by
  exact Returning.return_step FramedFind.machine.program returns outside 6 rfl _ _ _

theorem return_missing (query portCount edges vertices vertexCount : List Bool) :
    machine.computer.step (config (.inl 8) [] query portCount edges vertices [] vertexCount) =
      some (config (.inr 6) [] query portCount edges vertices [] vertexCount) := by
  exact Returning.return_step FramedFind.machine.program returns outside 8 rfl _ _ _

private theorem clear_generic
    (step : Cfg Stack Label FramedFind.Caller → Option (Cfg Stack Label FramedFind.Caller))
    (hs : ExecutesAt step (.inr 6) (clearStmt (.inl 6) (.inr 6) (.inr 7)))
    (query portCount edges vertices vertexCount : List Bool) :
    RunsExactly step (config (.inr 6) [] query portCount edges vertices [] vertexCount)
      (config (.inr 7) [] query [] edges vertices [] vertexCount) (portCount.length + 1) := by
  have empty : step (config (.inr 6) [] query [] edges vertices [] vertexCount) =
      some (config (.inr 7) [] query [] edges vertices [] vertexCount) := by
    rw [config, WordEqual.cfg, hs]
    simp [clearStmt, TM2.stepAux, config, WordEqual.cfg, WordEqual.clean, tapes, FramedFind.tapes, extras,
      -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  have cons (bit : Bool) (rest : List Bool) :
      step (config (.inr 6) [] query (bit :: rest) edges vertices [] vertexCount) =
        some (config (.inr 6) [] query rest edges vertices [] vertexCount) := by
    rw [config, WordEqual.cfg, hs]
    simp [clearStmt, TM2.stepAux, config, WordEqual.cfg, WordEqual.clean, tapes, FramedFind.tapes, extras,
      -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
    congr 2
    funext k
    cases k with
    | inl k => fin_cases k <;> simp [Function.update_apply, tapes, FramedFind.tapes, extras]
    | inr k => fin_cases k <;> simp [Function.update_apply, tapes, FramedFind.tapes, extras]
  induction portCount with
  | nil => exact runsExactly_one empty
  | cons bit rest ih => exact (runsExactly_one (cons bit rest)).trans ih

theorem clear_ports (query portCount edges vertices vertexCount : List Bool) :
    RunsExactly machine.computer.step (config (.inr 6) [] query portCount edges vertices [] vertexCount)
      (config (.inr 7) [] query [] edges vertices [] vertexCount) (portCount.length + 1) :=
  clear_generic machine.computer.step at_clear query portCount edges vertices vertexCount

theorem next_vertex (query edges vertices vertexCount : List Bool) :
    machine.computer.step (config (.inr 7) [] query [] edges vertices [] vertexCount) =
      some (config (.inr 2) [] query [] edges vertices [] (true :: vertexCount)) := by
  have hs : ExecutesAt machine.computer.step (.inr (7 : Fin 11))
      (push (.inr 3) (fun _ => true) (goto (fun _ => .inr 2))) := by intro state tapes; rfl
  rw [config, WordEqual.cfg, hs]
  simp [config, WordEqual.cfg, TM2.stepAux, tapes, extras,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

/-- The prepared graph machine remains finite, and every transition is bounded
by a fixed number of elementary Boolean operations. -/
theorem program_budget (label : Label) : TM2Cost.budget (machine.program label) ≤ 8 := by
  cases label with
  | inl label => simpa only [machine, Returning.program, Returning.statement_budget] using FramedFind.program_budget label
  | inr phase => fin_cases phase <;> decide

end Holant.Complexity.GraphPreprocessing.NetworkLookup
