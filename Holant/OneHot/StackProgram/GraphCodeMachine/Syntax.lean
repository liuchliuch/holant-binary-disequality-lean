import Holant.OneHot.StackProgram.GraphCodeMachine.Actions
import Holant.OneHot.StackProgram.TreeEncoding

/-! A finite Boolean-stack postorder compiler. All pending recursion is stored in
framed action words; coefficient labels alone occur in finite control. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine
open Turing Computability Holant.Complexity StackProtocol
open Turing.TM2.Stmt
variable {A : Type} [Fintype A]

inductive Label (A : Type) where
  | fixed (phase : Fin 20)
  | second (first : A) (phase : Fin 3)
  | node (a b : A)
  | cons (p : A)
  | root (a : A)
  | emit (op : Op A)
  deriving Fintype

abbrev Config (A : Type) := Cfg (Fin 6) (Label A) Unit
abbrev Statement (A : Type) := Stmt (Fin 6) (Label A) Unit

def tapes (input pending reverseOutput output buffer scratch : List Bool) : Fin 6 → List Bool :=
  ![input, pending, reverseOutput, output, buffer, scratch]

def actionLabel : Action A → Label A
  | .tree => .fixed 5
  | .forest => .fixed 8
  | .closed => .fixed 12
  | .emit op => .emit op

def labelStmt (e : Encoding A Bool) (C : ℕ) (next : A → Label A) : Statement A :=
  Machine.Dispatch.decodeStmt 4 (fun bits => (e.decode bits).elim (.fixed 18) next) (.fixed 18) C []

def actionStmt (e : Encoding A Bool) (C : ℕ) : Statement A :=
  Machine.Dispatch.decodeStmt 4 (fun bits => (actionDecode e bits).elim (.fixed 18) actionLabel)
    (.fixed 18) (C + 8) []

def schedule (e : Encoding A Bool) (tasks : List (Action A)) : Statement A :=
  FixedFieldMachines.Constant.pushWord 1 (records (actionEncoding e) tasks) (goto (fun _ => .fixed 1))

def emitCode (e : Encoding A Bool) (code : Code A) : Statement A :=
  FixedFieldMachines.Constant.pushWord 2 (records (opEncoding e) code).reverse (goto (fun _ => .fixed 1))

def forestMarker : Statement A :=
  pop 0 (fun v b => (b,v.2)) (branch (fun v => v.1.isSome)
    (branch (fun v => v.1.getD false)
      (load (fun v => (none,v.2)) (goto (fun _ => .fixed 9)))
      (load (fun v => (none,v.2)) (goto (fun _ => .fixed 19))))
    (load (fun v => (none,v.2)) (goto (fun _ => .fixed 18))))

def finishInput : Statement A :=
  pop 0 (fun v b => (b,v.2)) (branch (fun v => v.1.isSome)
    (load (fun v => (none,v.2)) (goto (fun _ => .fixed 18)))
    (push 2 (fun _ => false) (load (fun v => (none,v.2)) (goto (fun _ => .fixed 16)))))

def program (e : Encoding A Bool) (C : ℕ) (entry : Action A) : Label A → Statement A
  | .fixed i => match i.val with
    | 0 => FixedFieldMachines.Constant.pushWord 1 ((workEncoding e).encode [entry]) (goto (fun _ => .fixed 1))
    | 1 => Machine.Dispatch.fetchStmt 1 (.fixed 2) (.fixed 15) (.fixed 18)
    | 2 => GraphPreprocessing.Frame.scanStmt 1 5 (.fixed 2) (.fixed 3) (.fixed 18)
    | 3 => copyMoveStmt 5 4 (.fixed 3) (.fixed 4)
    | 4 => actionStmt e C
    | 5 => GraphPreprocessing.Frame.scanStmt 0 5 (.fixed 5) (.fixed 6) (.fixed 18)
    | 6 => copyMoveStmt 5 4 (.fixed 6) (.fixed 7)
    | 7 => labelStmt e C (fun a => .second a 0)
    | 8 => forestMarker
    | 9 => GraphPreprocessing.Frame.scanStmt 0 5 (.fixed 9) (.fixed 10) (.fixed 18)
    | 10 => copyMoveStmt 5 4 (.fixed 10) (.fixed 11)
    | 11 => labelStmt e C Label.cons
    | 12 => GraphPreprocessing.Frame.scanStmt 0 5 (.fixed 12) (.fixed 13) (.fixed 18)
    | 13 => copyMoveStmt 5 4 (.fixed 13) (.fixed 14)
    | 14 => labelStmt e C Label.root
    | 15 => finishInput
    | 16 => copyMoveStmt 2 3 (.fixed 16) (.fixed 17)
    | 19 => emitCode e [.zero, .one]
    | _ => .halt
  | .second a i => match i.val with
    | 0 => GraphPreprocessing.Frame.scanStmt 0 5 (.second a 0) (.second a 1) (.fixed 18)
    | 1 => copyMoveStmt 5 4 (.second a 1) (.second a 2)
    | _ => labelStmt e C (Label.node a)
  | .node a b => schedule e (nodeTasks a b)
  | .cons p => schedule e (consTasks p)
  | .root a => schedule e (closedTasks a)
  | .emit op => emitCode e [op]

abbrev machine (e : Encoding A Bool) (C : ℕ) (entry : Action A) : BinaryCompose.Machine where
  K := Fin 6
  input := 0
  output := 3
  Label := Label A
  main := .fixed 0
  State := Option Bool × Unit
  initial := (none, ())
  program := program e C entry

end Holant.OneHot.StackProgram.GraphCodeMachine
