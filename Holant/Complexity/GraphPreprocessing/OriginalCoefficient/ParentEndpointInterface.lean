import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentEndpoint

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentEndpoint
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.Computable
open Traversal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem read_parent (component depth edge : ℕ) (side : Bool) :
    RunsExactly (TM2.step program)
      (config (.inl 0) (ParentRowEncoding.row.encode ⟨component,depth,some (edge,side)⟩) [] [] [])
      (config (.inr 0) [] (List.replicate edge true) [] [side]) (component+depth+2*edge+8) := by
  have h := Returning.run_active ParentRead.program returns controller _ _ (Fin.elim0 : Fin 0 → List Bool) _
    (ParentRead.parent_exact component depth edge side) rfl
  have ret := Returning.return_step ParentRead.program returns controller (8 : Fin 11) rfl
    (none,()) (ParentRead.tapes [] (List.replicate edge true) [] [side]) (Fin.elim0 : Fin 0 → List Bool)
  change RunsExactly (TM2.step program) _ _ _ at h
  change TM2.step program _ = _ at ret
  have all := h.trans (runsExactly_one ret)
  have ht : component+depth+2*edge+8 = 1+(component+depth+2*edge+7) := by omega
  rw [ht]
  exact all

theorem read_root (component depth : ℕ) :
    RunsExactly (TM2.step program)
      (config (.inl 0) (ParentRowEncoding.row.encode ⟨component,depth,none⟩) [] [] [])
      (config (.inr 4) [] [] [] []) (component+depth+5) := by
  have h := Returning.run_active ParentRead.program returns controller _ _ (Fin.elim0 : Fin 0 → List Bool) _
    (ParentRead.root_exact component depth) rfl
  have ret := Returning.return_step ParentRead.program returns controller (7 : Fin 11) rfl
    (none,()) (ParentRead.tapes [] [] [] []) (Fin.elim0 : Fin 0 → List Bool)
  change RunsExactly (TM2.step program) _ _ _ at h
  change TM2.step program _ = _ at ret
  simpa [Returning.cfg,ParentRead.config,config,tapes,returns,cfg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    h.trans (runsExactly_one ret)

/-- A physical frame emitter consumes the extracted edge while retaining the
single orientation bit; no numeral is decoded or re-encoded by the caller. -/
theorem frame_edge (edge : List Bool) (side : Bool) :
    RunsExactly (TM2.step program)
      (config (.inr 0) [] edge [] [side])
      (config (.inr 3) [] [] [] (Holant.Algebraic.frame edge ++ [side])) (2*edge.length+3) := by
  have run := FixedFieldMachines.FrameEmit.prepend_exact (Sum.inl 1 : Stack) (.inl 3) (.inl 2)
    (by decide) (by decide) (by decide) (TM2.step program) (.inr 0) (.inr 1) (.inr 2) (.inr 3)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (tapes [] [] [] []) edge [side]
  simpa only [config,tapes3,update_edge,update_output,update_scratch] using run

def ticks (r : Graph.ParentRow) : ℕ := match r.parent with
  | none => r.component+r.depth+6
  | some (edge,_) => r.component+r.depth+4*edge+12

/-- Every canonical row has an actual complete clean execution. -/
theorem exact_run (r : Graph.ParentRow) :
    RunsExactly machine.computer.step
      (initList machine.computer (ParentRowEncoding.row.encode r))
      (haltList machine.computer (ParentRowEncoding.parent.encode r.parent)) (ticks r) := by
  rcases r with ⟨component,depth,parent⟩
  cases parent with
  | none =>
    have all := (read_root component depth).trans (runsExactly_one (halt_tag false []))
    rw [initial]
    simpa only [machine,FinTM2.step,ticks,ParentRowEncoding.parent_none,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  | some p =>
    rcases p with ⟨edge,side⟩
    have all := ((read_parent component depth edge side).trans (frame_edge (List.replicate edge true) side)).trans
      (runsExactly_one (halt_tag true (Holant.Algebraic.frame (List.replicate edge true) ++ [side])))
    have ht : ticks ⟨component,depth,some (edge,side)⟩ =
        1+((2*(List.replicate edge true).length+3)+(component+depth+2*edge+8)) := by
      simp only [ticks,List.length_replicate]; omega
    rw [initial,ht]
    simpa only [machine,FinTM2.step,ParentRowEncoding.parent_some] using all

theorem ticks_le (r : Graph.ParentRow) : ticks r ≤ 2*(ParentRowEncoding.row.encode r).length+2 := by
  rcases r with ⟨component,depth,parent⟩
  cases parent with
  | none =>
    simp only [ticks,ParentRowEncoding.row_word,ParentRowEncoding.parent_none,List.length_append,
      Holant.Algebraic.frame_length,List.length_replicate,List.length_singleton]
    omega
  | some p =>
    rcases p with ⟨edge,side⟩
    simp only [ticks,ParentRowEncoding.row_word,ParentRowEncoding.parent_some,List.length_append,
      Holant.Algebraic.frame_length,List.length_replicate,List.length_singleton,List.length_cons]
    omega

noncomputable def computes : Computes ParentRowEncoding.row ParentRowEncoding.parent Graph.ParentRow.parent where
  machine := machine
  time := 2*Polynomial.X+2
  outputs r := {
    steps := ticks r
    evals_in_steps := exact_run r
    steps_le_m := by simpa using ticks_le r }

theorem inFP : InFP ParentRowEncoding.row ParentRowEncoding.parent Graph.ParentRow.parent := computes.inFP

/-- For a literal original parent-table row, this output is its stored original
edge and child-end orientation, including the root's none marker. -/
theorem original_row (g : Graph) (v : g.Vertex) :
    RunsExactly machine.computer.step
      (initList machine.computer (ParentRowEncoding.row.encode
        (g.parentTable.get (Fin.cast g.parentTable_length.symm v))))
      (haltList machine.computer (ParentRowEncoding.parent.encode (g.parentRow v).parent))
      (ticks (g.parentRow v)) := by
  rw [ParentRowEncoding.original_row]
  exact exact_run _

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentEndpoint
