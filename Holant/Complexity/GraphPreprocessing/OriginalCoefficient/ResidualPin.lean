import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortBounds
import Holant.Complexity.GraphPreprocessing.ResidualLabel
import Holant.Complexity.GraphPreprocessing.Traversal.CallExits
import Holant.OneHot.StackProgram.Machine.StackWord

/-! Physical derivation of one residual pin at a queried original vertex. The
original endpoint is searched in the raw input, its returned vertex is compared
bitwise with the target, and only a matching original local port is emitted. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxRecDepth 4096

abbrev Stack := PortLookup.Stack ⊕ Fin 4
abbrev Label := PortLookup.Label ⊕ Fin 10
abbrev Statement := WordEqual.Statement Stack Label Unit

def targetKey : Stack := .inr 0
def compareKey : Stack := .inr 1
def temporaryKey : Stack := .inr 2
def outputKey : Stack := .inr 3
def rawKey : Stack := .inl PortLookup.rawKey
def queryKey : Stack := .inl PortLookup.queryKey
def vertexKey : Stack := .inl PortLookup.vertexKey
def portKey : Stack := .inl PortLookup.portKey

def returns (l : PortLookup.Label) : Fin 10 := if l = .inr 8 then 0 else 9

def controller (value : Bool) (i : Fin 10) : Statement := match i.val with
  | 0 => copyMoveStmt targetKey temporaryKey (.inr 0) (.inr 1)
  | 1 => copyRestoreStmt targetKey compareKey temporaryKey (.inr 1) (.inr 2)
  | 2 => WordEqual.statement vertexKey compareKey (.inr 2) (.inr 3) (.inr 6)
  | 3 => copyMoveStmt portKey temporaryKey (.inr 3) (.inr 4)
  | 4 => copyMoveStmt temporaryKey outputKey (.inr 4) (.inr 5)
  | 5 => push outputKey (fun _ => value) (push outputKey (fun _ => true)
      (load (fun _ => WordEqual.clean true ()) (goto (fun _ => .inr 8))))
  | 6 => clearStmt portKey (.inr 6) (.inr 7)
  | 7 => push outputKey (fun _ => false) (load (fun _ => WordEqual.clean true ()) (goto (fun _ => .inr 8)))
  | _ => .halt

def program (value : Bool) : Label → Statement := Returning.program PortLookup.program returns (controller value)

abbrev machine (value : Bool) : BinaryCompose.Machine where
  K := Stack
  input := rawKey
  output := outputKey
  Label := Label
  main := .inl (.inr 0)
  State := WordEqual.Memory Unit
  initial := WordEqual.clean true ()
  program := program value

def work (raw query vertex port target compare temporary output : List Bool) : Stack → List Bool :=
  Sum.elim (PortLookup.tapes [] [] port [] [] vertex raw query []) ![target,compare,temporary,output]

def config (label : Label) (same : Bool) (raw query vertex port target compare temporary output : List Bool) :=
  WordEqual.cfg label same () (work raw query vertex port target compare temporary output)

def pinWord (value : Bool) (vertex target port : ℕ) : List Bool :=
  if vertex = target then true :: value :: List.replicate port true else [false]

theorem lookup {s b : ℕ} {arity : ℕ → ℕ} (value : Bool) (r : RawClosedNetwork)
    (h : r.WellFormed s b arity) (p : r.Ports arity) (target output : List Bool) :
    let raw := RawClosedNetwork.encoding.encode r
    let query := RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)
    RunsExactly (machine value).computer.step
      (config (.inl (.inr 0)) true raw query [] [] target [] [] output)
      (config (.inr 0) true raw query (List.replicate p.1.val true) (List.replicate p.2.val true)
        target [] [] output) (PortLookup.ticks r h p + 1) := by
  have run := Returning.run_active PortLookup.program returns (controller value) _ _
    ![target,[],[],output] _ (PortLookup.exact_run r h p) rfl
  have ret := Returning.return_step PortLookup.program returns (controller value) (.inr 8) rfl
    (WordEqual.clean true ()) (PortLookup.tapes [] [] (List.replicate p.2.val true) [] []
      (List.replicate p.1.val true) (RawClosedNetwork.encoding.encode r)
      (RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)) []) ![target,[],[],output]
  change RunsExactly (machine value).computer.step _ _ _ at run
  change (machine value).computer.step _ = _ at ret
  simpa [Returning.cfg,PortLookup.config,config,work,returns,WordEqual.cfg,WordEqual.clean,Nat.add_comm] using
    run.trans (runsExactly_one ret)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
