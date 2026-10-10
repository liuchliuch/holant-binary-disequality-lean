import Holant.Complexity.GraphPreprocessing.UnaryBinary
import Holant.Complexity.GraphPreprocessing.Primitive
import Holant.Complexity.BinaryCompose.Interface

/-! The least true bitmap position is counted by physical unary tokens. The
remaining input is erased; an all-false or empty bitmap has a distinct error
state. This is a literal finite scan, with no host minimum operation. -/
open Holant.Complexity Holant.Complexity.GraphPreprocessing

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.FirstTrue
open Turing Computability StackProtocol BinaryCompose
open Turing.TM2.Stmt
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

def scan : Stmt (Fin 2) (Fin 4) Unit :=
  pop 0 (fun v bit => (bit,v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun _ => (none,())) (goto (fun _ => 1)))
        (push 1 (fun _ => true) (load (fun _ => (none,())) (goto (fun _ => 0)))))
      (load (fun _ => (none,())) (goto (fun _ => 3))))

def program (label : Fin 4) : Stmt (Fin 2) (Fin 4) Unit :=
  if label=0 then scan else if label=1 then clearStmt 0 1 2
    else if label=3 then load (fun _ => (some false,())) .halt else .halt

abbrev machine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Fin 4
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program := program

def tapes (input output : List Bool) : Fin 2 → List Bool := ![input,output]
def config (label : Fin 4) (input output : List Bool) := cfg label () (tapes input output)

@[simp] theorem update_input (input output word : List Bool) :
    Function.update (tapes input output) 0 word = tapes word output := by funext k; fin_cases k <;> simp [tapes,Function.update]
@[simp] theorem update_output (input output word : List Bool) :
    Function.update (tapes input output) 1 word = tapes input word := by funext k; fin_cases k <;> simp [tapes,Function.update]

theorem step_false (input output : List Bool) :
    TM2.step program (config 0 (false::input) output) = some (config 0 input (true::output)) := by
  change some (⟨some 0,(none,()),Function.update (Function.update (tapes (false::input) output) 0 input) 1 (true::output)⟩ : machine.Config) = _
  rw [update_input,update_output]; rfl
theorem step_true (input output : List Bool) :
    TM2.step program (config 0 (true::input) output) = some (config 1 input output) := by
  change some (⟨some 1,(none,()),Function.update (tapes (true::input) output) 0 input⟩ : machine.Config) = _
  rw [update_input]; rfl
theorem step_empty (output : List Bool) : TM2.step program (config 0 [] output) = some (config 3 [] output) := by
  change some (⟨some 3,(none,()),Function.update (tapes [] output) 0 []⟩ : machine.Config) = _
  rw [update_input]; rfl

theorem scan_prefix (n : ℕ) (suffix output : List Bool) :
    RunsExactly (TM2.step program) (config 0 (List.replicate n false++true::suffix) output)
      (config 1 suffix (List.replicate n true++output)) (n+1) := by
  induction n generalizing output with
  | zero => simpa using runsExactly_one (step_true suffix output)
  | succ n ih =>
    have h := (runsExactly_one (step_false (List.replicate n false++true::suffix) output)).trans (ih (true::output))
    have hw : List.replicate n true++true::output = List.replicate (n+1) true++output := by rw [List.replicate_succ']; simp
    simpa only [List.replicate_succ,List.cons_append,hw,Nat.add_assoc] using h

abbrev Input := {bits : List Bool // true∈bits}
def inputEncoding : Encoding Input Bool where
  encode x := x.val
  decode bits := if h : true∈bits then some ⟨bits,h⟩ else none
  decode_encode x := by simp [x.property]
def value (x : Input) : ℕ := x.val.findIdx id

theorem decomposition (bits : List Bool) (h : true∈bits) :
    ∃ suffix, bits = List.replicate (bits.findIdx id) false++true::suffix := by
  induction bits with
  | nil => simp at h
  | cons bit bits ih =>
    cases bit with
    | false =>
      have ht : true∈bits := by simpa using h
      obtain ⟨suffix,hs⟩ := ih ht
      refine ⟨suffix,?_⟩
      simpa only [List.findIdx_cons,id_eq,Bool.false_eq_true,↓reduceIte,
        List.replicate_succ,List.cons_append] using congrArg (List.cons false) hs
    | true => exact ⟨bits,by simp [List.findIdx_cons]⟩

theorem clear (input output : List Bool) :
    RunsExactly (TM2.step program) (config 1 input output) (config 2 [] output) (input.length+1) := by
  have h := clear_exact (TM2.step program) (0 : Fin 2) 1 2
    (executesAt_tm2 _ _ _ rfl) () (tapes input output)
  rw [update_input] at h
  exact h

theorem tapes_empty : tapes [] [] = fun _ => [] := by funext k; fin_cases k <;> rfl

theorem initial (input : List Bool) : initList machine.computer input = config 0 input [] := by
  rw [Machine.init_eq]
  have h := update_input [] [] input
  rw [tapes_empty] at h
  change wordTape (0 : Fin 2) input = _ at h
  change (⟨some 0,(none,()),wordTape (0 : Fin 2) input⟩ : machine.Config) = _
  rw [h]; rfl

theorem finish (output : List Bool) : TM2.step program (config 2 [] output) =
    some (haltList machine.computer output) := by
  rw [Machine.halt_eq]
  have h := update_output [] [] output
  rw [tapes_empty] at h
  change wordTape (1 : Fin 2) output = _ at h
  change some (⟨none,(none,()),tapes [] output⟩ : machine.Config) = _
  rw [←h]

theorem exact_run (x : Input) :
    RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode x))
      (haltList machine.computer (UnaryBinary.unaryEncoding.encode (value x))) (x.val.length+2) := by
  obtain ⟨suffix,hs⟩ := decomposition x.val x.property
  have scan := scan_prefix (value x) suffix []
  simp only [List.append_nil] at scan
  have all := (scan.trans
    (clear suffix (List.replicate (value x) true))).trans
    (runsExactly_one (finish (List.replicate (value x) true)))
  have hl : x.val.length+2 = 1+((suffix.length+1)+(value x+1)) := by
    have he := congrArg List.length hs
    simp only [List.length_append,List.length_replicate,List.length_cons] at he
    unfold value; omega
  rw [initial,hl]
  change RunsExactly (TM2.step program) (config 0 x.val []) _ _
  rw [hs]
  exact all

noncomputable def computes : Computes inputEncoding UnaryBinary.unaryEncoding value where
  machine := machine
  time := Polynomial.X+2
  outputs x := {
    steps := x.val.length+2
    evals_in_steps := exact_run x
    steps_le_m := by simp [inputEncoding] }

theorem inFP : InFP inputEncoding UnaryBinary.unaryEncoding value := computes.inFP

theorem program_budget (label : Fin 4) : TM2Cost.budget (program label) ≤ 7 := by
  fin_cases label <;> simp [program,scan,clearStmt,TM2Cost.budget]

theorem primitive_bound (x : Input) :
    (Primitive.run program (x.val.length+2) (some (initList machine.computer x.val))).2 =
      some (haltList machine.computer (List.replicate (value x) true)) ∧
    (Primitive.run program (x.val.length+2) (some (initList machine.computer x.val))).1 ≤
      7*(x.val.length+2) :=
  Primitive.execution_cost program 7 program_budget _ _ _ (exact_run x)

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.FirstTrue
