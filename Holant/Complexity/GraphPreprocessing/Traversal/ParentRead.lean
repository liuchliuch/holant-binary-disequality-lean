import Holant.Complexity.GraphPreprocessing.ParentRowEncoding
import Holant.Complexity.GraphPreprocessing.ListScan
import Holant.Complexity.GraphPreprocessing.Frame
import Holant.Complexity.GraphPreprocessing.Primitive

/-! Finite extraction of original parent edge/end fields from the frozen parent
row format. Component/rank frames are really skipped; the parent edge frame is
really copied in order. Root, selected parent, and malformed exits are distinct.
This is a returning primitive for the forthcoming original child scan. -/
namespace Holant.Complexity.GraphPreprocessing.Traversal.ParentRead
open Turing Computability StackProtocol Holant.Algebraic
open Turing.TM2.Stmt
abbrev Statement := Stmt (Fin 4) (Fin 11) Unit

def check (good : Fin 11) : Statement :=
  pop 0 (fun v b => (b,v.2)) (branch (fun v => v.1.isSome)
    (load (fun _ => (none,())) (goto (fun _ => 9)))
    (load (fun _ => (none,())) (goto (fun _ => good))))

def program (label : Fin 11) : Statement :=
  if label = 0 then ListScan.skipStmt 0 0 1 9
  else if label = 1 then ListScan.skipStmt 0 1 2 9
  else if label = 2 then
    pop 0 (fun v b => (b,v.2)) (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun _ => (none,())) (goto (fun _ => 3)))
        (load (fun _ => (none,())) (goto (fun _ => 6))))
      (load (fun _ => (none,())) (goto (fun _ => 9))))
  else if label = 3 then Frame.scanStmt 0 2 3 4 9
  else if label = 4 then copyMoveStmt 2 1 4 5
  else if label = 5 then
    pop 0 (fun v b => (b,v.2)) (branch (fun v => v.1.isSome)
      (push 3 (fun v => v.1.getD false) (load (fun _ => (none,())) (goto (fun _ => 10))))
      (load (fun _ => (none,())) (goto (fun _ => 9))))
  else if label = 6 then check 7
  else if label = 10 then check 8
  else .halt

abbrev machine : BinaryCompose.Machine where
  K := Fin 4
  input := 0
  output := 1
  Label := Fin 11
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def tapes (input edge scratch orientation : List Bool) : Fin 4 → List Bool := ![input,edge,scratch,orientation]
def config (label : Fin 11) (input edge scratch orientation : List Bool) : machine.Config :=
  cfg label () (tapes input edge scratch orientation)

theorem skip_component (word suffix edge orientation : List Bool) :
    RunsExactly machine.computer.step (config 0 (frame word ++ suffix) edge [] orientation)
      (config 1 suffix edge [] orientation) (word.length+1) := by
  have hs : ExecutesAt machine.computer.step (0 : Fin 11) (ListScan.skipStmt 0 0 1 9) := by intro state tapes; rfl
  have h := ListScan.skip_exact (0 : Fin 4) 1 (by decide) machine.computer.step 0 1 9 hs ()
    (tapes [] [] [] orientation) word suffix edge
  convert h using 1 <;> unfold config <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem skip_depth (word suffix edge orientation : List Bool) :
    RunsExactly machine.computer.step (config 1 (frame word ++ suffix) edge [] orientation)
      (config 2 suffix edge [] orientation) (word.length+1) := by
  have hs : ExecutesAt machine.computer.step (1 : Fin 11) (ListScan.skipStmt 0 1 2 9) := by intro state tapes; rfl
  have h := ListScan.skip_exact (0 : Fin 4) 1 (by decide) machine.computer.step 1 2 9 hs ()
    (tapes [] [] [] orientation) word suffix edge
  convert h using 1 <;> unfold config <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem parent_tag (b : Bool) (suffix : List Bool) :
    machine.computer.step (config 2 (b::suffix) [] [] []) = some (config (if b then 3 else 6) suffix [] [] []) := by
  cases b <;> simp [machine,FinTM2.step,TM2.step,program,config,cfg,TM2.stepAux,tapes]
  all_goals congr 2; funext k; fin_cases k <;> rfl

theorem edge_exact (word suffix : List Bool) :
    RunsExactly machine.computer.step (config 3 (frame word ++ suffix) [] [] [])
      (config 5 suffix word [] []) (2*(word.length+1)) := by
  have hs : ExecutesAt machine.computer.step (3 : Fin 11) (Frame.scanStmt 0 2 3 4 9) := by intro state tapes; rfl
  have hr : ExecutesAt machine.computer.step (4 : Fin 11) (copyMoveStmt 2 1 4 5) := by intro state tapes; rfl
  have h := Frame.extract_exact (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step 3 4 5 9 hs hr () (fun _ => []) word suffix []
  simp only [List.append_nil] at h
  convert h using 1 <;> unfold config <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem orientation_bit (b : Bool) (suffix edge : List Bool) :
    machine.computer.step (config 5 (b::suffix) edge [] []) = some (config 10 suffix edge [] [b]) := by
  simp [machine,FinTM2.step,TM2.step,program,config,cfg,TM2.stepAux,tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem check_empty (edge orientation : List Bool) :
    machine.computer.step (config 10 [] edge [] orientation) = some (config 8 [] edge [] orientation) := by
  simp [machine,FinTM2.step,TM2.step,program,check,config,cfg,TM2.stepAux,tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem check_root : machine.computer.step (config 6 [] [] [] []) = some (config 7 [] [] [] []) := by
  simp [machine,FinTM2.step,TM2.step,program,check,config,cfg,TM2.stepAux,tapes]
  congr 2; funext k; fin_cases k <;> rfl

/-- A genuine root is distinguished from every edge/end, including edge0,false. -/
theorem root_exact (component depth : ℕ) :
    RunsExactly machine.computer.step
      (config 0 (ParentRowEncoding.row.encode ⟨component,depth,none⟩) [] [] [])
      (config 7 [] [] [] []) (component+depth+4) := by
  have h := (((skip_component (List.replicate component true)
      (frame (List.replicate depth true) ++ [false]) [] []).trans
    (skip_depth (List.replicate depth true) [false] [] [])).trans
    (runsExactly_one (parent_tag false []))).trans (runsExactly_one check_root)
  simpa [ParentRowEncoding.row_word,ParentRowEncoding.parent_none,List.append_assoc,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Literal original edge index and its selected child end are physically read. -/
theorem parent_exact (component depth edge : ℕ) (orientation : Bool) :
    RunsExactly machine.computer.step
      (config 0 (ParentRowEncoding.row.encode ⟨component,depth,some (edge,orientation)⟩) [] [] [])
      (config 8 [] (List.replicate edge true) [] [orientation]) (component+depth+2*edge+7) := by
  have h := (((((skip_component (List.replicate component true)
      (frame (List.replicate depth true) ++ true :: (frame (List.replicate edge true) ++ [orientation])) [] []).trans
    (skip_depth (List.replicate depth true) (true :: (frame (List.replicate edge true) ++ [orientation])) [] [])).trans
    (runsExactly_one (parent_tag true (frame (List.replicate edge true) ++ [orientation])))).trans
    (edge_exact (List.replicate edge true) [orientation])).trans
    (runsExactly_one (orientation_bit orientation [] (List.replicate edge true)))).trans
    (runsExactly_one (check_empty (List.replicate edge true) [orientation]))
  convert h using 1
  · simp [ParentRowEncoding.row_word,ParentRowEncoding.parent_some,List.append_assoc]
  · simp only [List.length_replicate]; omega

theorem program_budget (label : Fin 11) : TM2Cost.budget (program label) ≤ 8 := by fin_cases label <;> decide

theorem parent_bit_cost (component depth edge : ℕ) (orientation : Bool) :
    (Primitive.run program (component+depth+2*edge+7)
      (some (config 0 (ParentRowEncoding.row.encode ⟨component,depth,some (edge,orientation)⟩) [] [] []))).2 =
      some (config 8 [] (List.replicate edge true) [] [orientation]) ∧
    (Primitive.run program (component+depth+2*edge+7)
      (some (config 0 (ParentRowEncoding.row.encode ⟨component,depth,some (edge,orientation)⟩) [] [] []))).1 ≤
      8*(component+depth+2*edge+7) :=
  Primitive.execution_cost program 8 program_budget _ _ _ (parent_exact component depth edge orientation)

/-- The source-derived root path has the same primitive accounting. -/
theorem root_bit_cost (component depth : ℕ) :
    (Primitive.run program (component+depth+4)
      (some (config 0 (ParentRowEncoding.row.encode ⟨component,depth,none⟩) [] [] []))).2 =
      some (config 7 [] [] [] []) ∧
    (Primitive.run program (component+depth+4)
      (some (config 0 (ParentRowEncoding.row.encode ⟨component,depth,none⟩) [] [] []))).1 ≤
      8*(component+depth+4) :=
  Primitive.execution_cost program 8 program_budget _ _ _ (root_exact component depth)

/-- Missing or excess end bits reject before a selected-parent return. This is
framing/field extraction; canonical unary validity comes from the source codec. -/
theorem missing_orientation (edge : List Bool) :
    machine.computer.step (config 5 [] edge [] []) = some (config 9 [] edge [] []) := by
  simp [machine,FinTM2.step,TM2.step,program,config,cfg,TM2.stepAux,tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem excess_orientation (b : Bool) (tail edge orientation : List Bool) :
    machine.computer.step (config 10 (b::tail) edge [] orientation) =
      some (config 9 tail edge [] orientation) := by
  simp [machine,FinTM2.step,TM2.step,program,check,config,cfg,TM2.stepAux,tapes]
  congr 2; funext k; fin_cases k <;> rfl

end Holant.Complexity.GraphPreprocessing.Traversal.ParentRead
