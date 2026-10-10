import Holant.Complexity.GraphPreprocessing.NetworkLookupOriginal

/-! Returning original-incidence lookup which preserves the physical raw input
and endpoint query. Both original vertex and local-port outputs are unary words;
all internal parsing and search stacks are explicitly cleared. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortLookup
open Turing Computability StackProtocol BinaryCompose Holant.Algebraic
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Stack := NetworkLookup.Stack ⊕ Fin 3
abbrev Label := NetworkLookup.Label ⊕ Fin 11
abbrev Caller := FramedFind.Caller
abbrev Statement := Stmt Stack Label Caller

def vertexKey : Stack := .inl (.inr 3)
def portKey : Stack := .inl (.inl 6)
def rawKey : Stack := .inr 0
def queryKey : Stack := .inr 1
def temporaryKey : Stack := .inr 2

def returns (label : NetworkLookup.Label) : Fin 11 :=
  if label = .inr 8 then 4 else if label = .inr 9 then 9 else 10

def controller (i : Fin 11) : Statement := match i.val with
  | 0 => copyMoveStmt rawKey temporaryKey (.inr 0) (.inr 1)
  | 1 => copyRestoreStmt rawKey (.inl (.inr 0)) temporaryKey (.inr 1) (.inr 2)
  | 2 => copyMoveStmt queryKey temporaryKey (.inr 2) (.inr 3)
  | 3 => copyRestoreStmt queryKey (.inl (.inl 1)) temporaryKey (.inr 3) (.inl (.inr 0))
  | 4 => clearStmt (.inl (.inl 0)) (.inr 4) (.inr 5)
  | 5 => clearStmt (.inl (.inl 1)) (.inr 5) (.inr 6)
  | 6 => clearStmt (.inl (.inr 0)) (.inr 6) (.inr 7)
  | 7 => clearStmt (.inl (.inr 1)) (.inr 7) (.inr 8)
  | _ => .halt

def program : Label → Statement := Returning.program NetworkLookup.machine.program returns controller

abbrev machine : BinaryCompose.Machine where
  K := Stack
  input := rawKey
  output := vertexKey
  Label := Label
  main := .inr 0
  State := WordEqual.Memory Unit
  initial := WordEqual.clean true ()
  program := program

def tapes (source workerQuery portCount input vertices vertexCount raw query temporary : List Bool) : Stack → List Bool :=
  Sum.elim (NetworkLookup.tapes source workerQuery portCount input vertices [] vertexCount) ![raw, query, temporary]

def config (label : Label) (source workerQuery portCount input vertices vertexCount raw query temporary : List Bool) : machine.Config :=
  WordEqual.cfg label true () (tapes source workerQuery portCount input vertices vertexCount raw query temporary)

theorem copy_raw (raw query : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 0) [] [] [] [] [] [] raw query [])
      (config (.inr 2) [] [] [] raw [] [] raw query []) (2 * (raw.length + 1)) := by
  have h := copy_exact_frame rawKey (.inl (.inr 0)) temporaryKey (by decide) (by decide) (by decide)
    machine.computer.step (.inr 0) (.inr 1) (.inr 2)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true, none, ())
    (tapes [] [] [] [] [] [] [] query []) raw []
  convert h using 1 <;> dsimp only [config,WordEqual.cfg,WordEqual.clean,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => cases k with
    | inl k => fin_cases k <;> simp [tapes3,tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,rawKey,temporaryKey,Function.update]
    | inr k => fin_cases k <;> simp [tapes3,tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,rawKey,temporaryKey,Function.update]
  | inr k => fin_cases k <;> simp [tapes3,tapes,rawKey,temporaryKey,Function.update]

theorem copy_query (raw query : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 2) [] [] [] raw [] [] raw query [])
      (config (.inl (.inr 0)) [] query [] raw [] [] raw query []) (2 * (query.length + 1)) := by
  have h := copy_exact_frame queryKey (.inl (.inl 1)) temporaryKey (by decide) (by decide) (by decide)
    machine.computer.step (.inr 2) (.inr 3) (.inl (.inr 0))
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (true, none, ())
    (tapes [] [] [] raw [] [] raw [] []) query []
  convert h using 1 <;> dsimp only [config,WordEqual.cfg,WordEqual.clean,cfg]
  all_goals congr 1 <;> funext k <;> cases k with
  | inl k => cases k with
    | inl k => fin_cases k <;> simp [tapes3,tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,queryKey,temporaryKey,Function.update]
    | inr k => fin_cases k <;> simp [tapes3,tapes,NetworkLookup.tapes,NetworkLookup.extras,FramedFind.tapes,queryKey,temporaryKey,Function.update]
  | inr k => fin_cases k <;> simp [tapes3,tapes,queryKey,temporaryKey,Function.update]

/-- The exact original-coordinate lookup is called on copied input words. -/
theorem lookup {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (p : r.Ports arity) :
    let raw := RawClosedNetwork.encoding.encode r
    let query := RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)
    RunsExactly machine.computer.step
      (config (.inl (.inr 0)) [] query [] raw [] [] raw query [])
      (config (.inr 4)
        (framedListEncode RawClosedNetwork.endpointEncoding ((r.vertices.get p.1).2.drop (p.2.val + 1))) query
        (List.replicate p.2.val true) (framedListEncode encodingNatBool r.edges)
        (framedListEncode RawClosedNetwork.vertexEncoding (r.vertices.drop (p.1.val + 1)))
        (List.replicate p.1.val true) raw query []) (NetworkLookup.portTime r h p + 1) := by
  have run := NetworkLookup.original_port_exact r h p
  have lifted := Returning.run_active NetworkLookup.machine.program returns controller _ _
    ![RawClosedNetwork.encoding.encode r, RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p), []] _ run rfl
  have ret := Returning.return_step NetworkLookup.machine.program returns controller (.inr 8) rfl
    (WordEqual.clean true ()) (NetworkLookup.portResult r h p).stk
    ![RawClosedNetwork.encoding.encode r, RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p), []]
  change RunsExactly machine.computer.step _ _ _ at lifted
  change machine.computer.step _ = _ at ret
  have all := lifted.trans (runsExactly_one ret)
  simpa [Returning.cfg,NetworkLookup.portInput,NetworkLookup.portResult,NetworkLookup.config,
    config,WordEqual.cfg,WordEqual.clean,cfg,tapes,returns,Nat.add_comm] using all

private theorem clear_stage (i j : Fin 11) (k : Stack) (before after : Stack → List Bool)
    (hp : machine.program (.inr i) = clearStmt k (.inr i) (.inr j))
    (he : Function.update before k [] = after) :
    RunsExactly machine.computer.step (WordEqual.cfg (.inr i) true () before)
      (WordEqual.cfg (.inr j) true () after) ((before k).length + 1) := by
  have h := clear_exact machine.computer.step k (.inr i) (.inr j)
    (executesAt_tm2 _ _ _ hp) (true, none, ()) before
  simpa only [WordEqual.cfg, WordEqual.clean, cfg, he] using h

/-- Every leftover parse stream and copied query is cleared physically. -/
theorem cleanup (source workerQuery portCount input vertices vertexCount raw query : List Bool) :
    RunsExactly machine.computer.step
      (config (.inr 4) source workerQuery portCount input vertices vertexCount raw query [])
      (config (.inr 8) [] [] portCount [] [] vertexCount raw query [])
      (source.length + workerQuery.length + input.length + vertices.length + 4) := by
  have h0 := clear_stage 4 5 (.inl (.inl 0))
    (tapes source workerQuery portCount input vertices vertexCount raw query []) (tapes [] workerQuery portCount input vertices vertexCount raw query []) rfl (by
      funext k; cases k with
      | inl k => cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl)
  have h1 := clear_stage 5 6 (.inl (.inl 1))
    (tapes [] workerQuery portCount input vertices vertexCount raw query []) (tapes [] [] portCount input vertices vertexCount raw query []) rfl (by
      funext k; cases k with
      | inl k => cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl)
  have h2 := clear_stage 6 7 (.inl (.inr 0))
    (tapes [] [] portCount input vertices vertexCount raw query []) (tapes [] [] portCount [] vertices vertexCount raw query []) rfl (by
      funext k; cases k with
      | inl k => cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl)
  have h3 := clear_stage 7 8 (.inl (.inr 1))
    (tapes [] [] portCount [] vertices vertexCount raw query []) (tapes [] [] portCount [] [] vertexCount raw query []) rfl (by
      funext k; cases k with
      | inl k => cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl)
  convert ((h0.trans h1).trans h2).trans h3 using 1 <;> first | rfl | (simp only [tapes, NetworkLookup.tapes, NetworkLookup.extras, FramedFind.tapes, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]; omega)

variable {s b : ℕ} {arity : ℕ → ℕ}

def ticks (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) : ℕ :=
  2 * (RawClosedNetwork.encoding.encode r).length +
    3 * (RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)).length +
    NetworkLookup.portTime r h p +
    (framedListEncode RawClosedNetwork.endpointEncoding ((r.vertices.get p.1).2.drop (p.2.val + 1))).length +
    (framedListEncode encodingNatBool r.edges).length +
    (framedListEncode RawClosedNetwork.vertexEncoding (r.vertices.drop (p.1.val + 1))).length + 9

/-- Exact clean returning lookup, preserving original raw bytes and endpoint bits. -/
theorem original_port_exact (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    let raw := RawClosedNetwork.encoding.encode r
    let query := RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)
    RunsExactly machine.computer.step
      (config (.inr 0) [] [] [] [] [] [] raw query [])
      (config (.inr 8) [] [] (List.replicate p.2.val true) [] [] (List.replicate p.1.val true) raw query [])
      (ticks r h p) := by
  have a := copy_raw (RawClosedNetwork.encoding.encode r) (RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p))
  have b := copy_query (RawClosedNetwork.encoding.encode r) (RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p))
  have c := lookup r h p
  have d := cleanup
    (framedListEncode RawClosedNetwork.endpointEncoding ((r.vertices.get p.1).2.drop (p.2.val + 1)))
    (RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p)) (List.replicate p.2.val true)
    (framedListEncode encodingNatBool r.edges)
    (framedListEncode RawClosedNetwork.vertexEncoding (r.vertices.drop (p.1.val + 1)))
    (List.replicate p.1.val true) (RawClosedNetwork.encoding.encode r)
    (RawClosedNetwork.endpointEncoding.encode (r.portEndpoint h p))
  convert ((a.trans b).trans c).trans d using 1
  unfold ticks
  omega

/-- Source edge IDs and end bits determine the physical original lookup target. -/
theorem endpoint_exact (r : RawClosedNetwork) (h : r.WellFormed s b arity) (q : Fin r.edges.length × Bool) :
    let p := r.lookup h q
    let raw := RawClosedNetwork.encoding.encode r
    let query := RawClosedNetwork.endpointEncoding.encode (q.1.val, q.2)
    RunsExactly machine.computer.step
      (config (.inr 0) [] [] [] [] [] [] raw query [])
      (config (.inr 8) [] [] (List.replicate p.2.val true) [] [] (List.replicate p.1.val true) raw query [])
      (ticks r h p) := by
  have hp : r.portEndpoint h (r.lookup h q) = (q.1.val, q.2) :=
    congrArg (fun p : Fin r.edges.length × Bool => (p.1.val, p.2)) (r.route_lookup h q)
  simpa only [hp] using original_port_exact r h (r.lookup h q)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.PortLookup
