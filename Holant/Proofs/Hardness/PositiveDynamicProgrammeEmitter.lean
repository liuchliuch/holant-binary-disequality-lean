import Holant.Proofs.Hardness.PositiveDynamicProgrammeFormulas
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Combinators
import Holant.Complexity.OracleBatch.EncodingBounds

/-! Physical Boolean emission and finite-field interpretation of the dynamic
formulas. Repetition invokes the contextual traversal machine and emits every
opcode and delimiter; formula evaluation uses the concrete field interpreter. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicProgrammeEmitter
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open BinaryInterpolation Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open PositiveDynamicProgrammeFormulas
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
abbrev unary := UnaryBinary.unaryEncoding
abbrev labels := SignatureLabel.binaryFinEncoding 6
abbrev Code := Holant.OneHot.StackProgram.Code Labels

def chunk (p : Code) : List Bool := entries (opEncoding labels) p
abbrev Emits {X : Type} (e : Encoding X Bool) (p : X → Formula) :=
  Computes e Frame.wordEncoding (fun x=>chunk (p x).code)

@[simp] theorem chunk_append (p q : Code) : chunk (p++q)=chunk p++chunk q := by
  simp [chunk,entries]

def constant {X : Type} (e : Encoding X Bool) (p : Formula) : Emits e (fun _=>p) :=
  constantComputes e Frame.wordEncoding (chunk p.code)

def add {X : Type} {e : Encoding X Bool} {p q : X→Formula}
    (wp : Emits e p) (wq : Emits e q) : Emits e (fun x=>.add (p x) (q x)) :=
  congrComputes (joinComputes (joinComputes wq wp)
    (constantComputes e Frame.wordEncoding (chunk [.add])))
    (fun _=>by simp [RingFormula.code,List.append_assoc])

def mul {X : Type} {e : Encoding X Bool} {p q : X→Formula}
    (wp : Emits e p) (wq : Emits e q) : Emits e (fun x=>.mul (p x) (q x)) :=
  congrComputes (joinComputes (joinComputes wq wp)
    (constantComputes e Frame.wordEncoding (chunk [.mul])))
    (fun _=>by simp [RingFormula.code,List.append_assoc])

theorem power_code (p : Formula) (n : ℕ) :
    (p.power n).code=[.one]++(List.replicate n (p.code++[.mul])).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [RingFormula.power,RingFormula.code,ih,List.replicate_succ',List.append_assoc]

theorem chunk_flatten (ps : List Code) : chunk ps.flatten=(ps.map chunk).flatten := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.flatten_cons,List.map_cons,chunk_append,ih]

/-- Both the exponent and the powered formula are emitted from the current input. -/
def power {X : Type} {e : Encoding X Bool} (n : X→ℕ) (wn : Computes e unary n)
    {p : X→Formula} (wp : Emits e p) : Emits e (fun x=>(p x).power (n x)) := by
  let body := joinComputes wp (constantComputes e Frame.wordEncoding (chunk [.mul]))
  let repeats := WeightCompiler.repeatWordsComputes e n wn _ body
  exact congrComputes (joinComputes (constantComputes e Frame.wordEncoding (chunk [.one])) repeats)
    (fun x=>by
      rw [power_code,chunk_append,chunk_flatten,List.map_replicate,chunk_append])

/-- Append the genuine list terminator before passing code to the interpreter. -/
def codeComputes {X : Type} {e : Encoding X Bool} {p : X→Formula} (wp : Emits e p) :
    Computes e (codeEncoding labels) (fun x=>(p x).code) :=
  recode (joinComputes wp (constantComputes e Frame.wordEncoding [false])) id (fun _=>rfl)
    (fun x=>by
      change chunk (p x).code++[false]=framedListEncode (opEncoding labels) (p x).code
      simpa only [chunk,List.append_nil,framedListEncode] using
        entries_append_encode (opEncoding labels) (p x).code [])

theorem size_le_code_length (p : Formula) : p.size≤((codeEncoding labels).encode p.code).length := by
  rw [←RingFormula.code_length]
  have h := OracleBatch.list_length_le (p.code.map (opEncoding labels).encode)
  simpa only [codeEncoding,List.length_map,OracleBatch.list_encode] using h

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ} (F : FixedField K d) (a b c : K)
def coordinates : Labels→Fin d→ℚ := fun i=>F.decode.symm (coefficients a b c i)
@[simp] theorem decode_coordinates (i : Labels) : F.decode (coordinates F a b c i)=coefficients a b c i := by
  simp [coordinates]

/-- A concrete emitter followed by the existing finite arithmetic interpreter.
No evaluation function, runtime witness, or completed run is supplied as data. -/
def evaluate {X : Type} {e : Encoding X Bool} {p : X→Formula} (wp : Emits e p) :
    Computes e F.encoding (fun x=>(p x).eval (coefficients a b c)) where
  machine := (codeComputes wp).machine.compose (RingFormulaMachine.machine F (coordinates F a b c) labels)
  time := (codeComputes wp).time+2*(codeComputes wp).outputBound.bound+2+
    (RingFormulaMachine.runtimePolynomial F (coordinates F a b c) labels).comp
      (codeComputes wp).outputBound.bound
  outputs x := by
    let first := (codeComputes wp).outputs x
    have hp : (p x).size≤(codeComputes wp).outputBound.bound.eval (e.encode x).length :=
      (size_le_code_length (p x)).trans ((codeComputes wp).outputBound.length_le x)
    have he : RingFormulaMachine.coefficients F (coordinates F a b c)=coefficients a b c := by
      funext i; exact decode_coordinates F a b c i
    have run : ∃ t, t≤(RingFormulaMachine.runtimePolynomial F (coordinates F a b c) labels).eval
        (p x).size ∧ Kernels.Executes (RingFormulaMachine.machine F (coordinates F a b c) labels)
          ((codeEncoding labels).encode (p x).code)
          (F.encoding.encode ((p x).eval (coefficients a b c))) t := by
      obtain ⟨t,ht,hr⟩ := RingFormulaMachine.evaluate_formula F (coordinates F a b c) labels 5
        (by simp) (p x)
      exact ⟨t,ht,by simpa only [he] using hr⟩
    let t := run.choose
    have ht := run.choose_spec.1
    have hr := run.choose_spec.2
    let last : TM2OutputsInTime (RingFormulaMachine.machine F (coordinates F a b c) labels).computer
        ((codeEncoding labels).encode (p x).code)
        (some (F.encoding.encode ((p x).eval (coefficients a b c))))
        ((RingFormulaMachine.runtimePolynomial F (coordinates F a b c) labels).eval
          (p x).size) := {steps:=t,steps_le_m:=ht,evals_in_steps:=hr}
    let all := Machine.compose_correct (codeComputes wp).machine
      (RingFormulaMachine.machine F (coordinates F a b c) labels) _ _ _ _ _ first last
    refine {steps:=all.steps,evals_in_steps:=all.evals_in_steps,steps_le_m:=?_}
    have htime := all.steps_le_m
    have hwidth := (codeComputes wp).outputBound.length_le x
    have hlast := natPolynomial_eval_mono
      (RingFormulaMachine.runtimePolynomial F (coordinates F a b c) labels) hp
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
    omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicProgrammeEmitter
