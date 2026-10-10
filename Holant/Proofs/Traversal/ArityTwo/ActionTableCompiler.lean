import Holant.Proofs.Traversal.ArityTwo.PortTableCompiler
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.LiteralBits
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
import Holant.Complexity.GraphPreprocessing.Traversal.PreparedBounds


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.ActionTableCompiler
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Context := ℕ × List Bool
def contextEncoding := pairEncoding UnaryBinary.unaryEncoding Frame.wordEncoding
def inputEncoding := pairEncoding contextEncoding PortInstruction.recordEncoding

def call (ctx : Context) (next : ℕ) : List Bool :=
  if next = ctx.1 then Traversal.literals ctx.2 else Traversal.reference next

def row (ctx : Context) (r : PortInstruction.Record) : List Bool :=
  if r.1 then Traversal.literals r.2.2
  else call ctx r.2.1 ++ Traversal.literals r.2.2

def context := Wiring.firstComputes contextEncoding PortInstruction.recordEncoding
def instruction := Wiring.secondComputes contextEncoding PortInstruction.recordEncoding
def flag := instruction.andThen
  (Wiring.firstComputes encodingBoolBool (pairEncoding UnaryBinary.unaryEncoding Frame.wordEncoding))
def body := instruction.andThen
  (Wiring.secondComputes encodingBoolBool (pairEncoding UnaryBinary.unaryEncoding Frame.wordEncoding))
def next := body.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding Frame.wordEncoding)
def payload := body.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding Frame.wordEncoding)
def cut := context.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding Frame.wordEncoding)
def base := context.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding Frame.wordEncoding)

def callComputes : Computes inputEncoding Frame.wordEncoding (fun x => call x.1 x.2.2.1) :=
  congrComputes (ifComputes ((pairComputes next cut).andThen (equalComputes UnaryBinary.unaryEncoding))
    (base.andThen LiteralBits.computes) (next.andThen ActionChild.referenceComputes))
    (fun _ => by simp [call])

def rowComputes : Computes inputEncoding Frame.wordEncoding (fun x => row x.1 x.2) :=
  ifComputes flag (payload.andThen LiteralBits.computes)
    (joinComputes callComputes (payload.andThen LiteralBits.computes))

def table (ctx : Context) (records : List PortInstruction.Record) := records.map (row ctx)

def tableComputes : Computes (pairEncoding contextEncoding (framedListEncoding PortInstruction.recordEncoding))
    (framedListEncoding Frame.wordEncoding) (fun x => table x.1 x.2) :=
  mapListComputes contextEncoding PortInstruction.recordEncoding Frame.wordEncoding row rowComputes

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)

def countComputes : Computes (RawPortQuery.encoding s b arity) UnaryBinary.unaryEncoding
    (fun x => 2*x.1.val.edges.length) := by
  let n := (RawPortQuery.sourceComputes s b arity).andThen (edgeCountComputes s b arity)
  exact recode (joinComputes (n.andThen (encodeComputes UnaryBinary.unaryEncoding))
    (n.andThen (encodeComputes UnaryBinary.unaryEncoding))) id (fun _ => rfl)
    (fun x => by
      change List.replicate x.1.val.edges.length true ++ List.replicate x.1.val.edges.length true =
        List.replicate (2 * x.1.val.edges.length) true
      rw [two_mul,List.replicate_add])

def queryContext (closed : Bool) (base : List Bool) (x : RawPortQuery.Input s b arity) : Context :=
  (if closed then EndpointAddress.value s b arity x else 2*x.1.val.edges.length,base)

def queryContextComputes (closed : Bool) (base : List Bool) :
    Computes (RawPortQuery.encoding s b arity) contextEncoding (queryContext s b arity closed base) := by
  cases closed with
  | false => exact (pairComputes (countComputes s b arity)
      (constantComputes (RawPortQuery.encoding s b arity) Frame.wordEncoding base))
  | true => exact (pairComputes (EndpointAddress.computes s b arity)
      (constantComputes (RawPortQuery.encoding s b arity) Frame.wordEncoding base))

def rows (closed : Bool) (base : List Bool) (x : RawPortQuery.Input s b arity) :=
  table (queryContext s b arity closed base x) (PortTableCompiler.value s b arity labels edges codec x.1)

def rowsComputes (closed : Bool) (base : List Bool) :
    Computes (RawPortQuery.encoding s b arity) (framedListEncoding Frame.wordEncoding)
      (rows s b arity labels edges codec closed base) :=
  (pairComputes (queryContextComputes s b arity closed base)
    ((RawPortQuery.sourceComputes s b arity).andThen
      (PortTableCompiler.computes s b arity labels edges codec))).andThen tableComputes

def prepared (closed : Bool) (base : List Bool) (x : RawPortQuery.Input s b arity) :=
  Traversal.preparedInput (rows s b arity labels edges codec closed base x)
    (Traversal.reference (EndpointAddress.value s b arity x))

/-- This provider really emits all pointer rows and the starting reference.
The source-counted expander then reads those exact bytes. -/
def prepareComputes (closed : Bool) (base : List Bool) :
    Computes (RawPortQuery.encoding s b arity) Frame.wordEncoding
      (prepared s b arity labels edges codec closed base) :=
  recode (pairComputes (rowsComputes s b arity labels edges codec closed base)
    ((EndpointAddress.computes s b arity).andThen ActionChild.referenceComputes))
    id (fun _ => rfl) (fun _ => rfl)

def machine (closed : Bool) (base : List Bool) : Machine :=
  (prepareComputes s b arity labels edges codec closed base).machine.compose Traversal.preparedMachine

theorem rows_length (closed : Bool) (base : List Bool) (x : RawPortQuery.Input s b arity) :
    (rows s b arity labels edges codec closed base x).length = 2*x.1.val.edges.length := by
  simp [rows,table,PortTableCompiler.length]

def timePolynomial (closed : Bool) (base : List Bool) : Polynomial ℕ :=
  let w := prepareComputes s b arity labels edges codec closed base
  w.time + (8*Polynomial.X^2+20*Polynomial.X+12).comp w.outputBound.bound

/-- Operational composition only: semantic path/cycle derivations must supply
the expansion relation from the already proved concrete port walk. This lemma
is deliberately not exported as an unconditional raw-network FP theorem. -/
theorem execute_expansion (closed : Bool) (base : List Bool) (x : RawPortQuery.Input s b arity)
    (out : List Bool) (n : ℕ)
    (h : Traversal.Expands (rows s b arity labels edges codec closed base x)
      (Traversal.reference (EndpointAddress.value s b arity x)) out n)
    (hn : n ≤ 2*x.1.val.edges.length) :
    ∃ time, time ≤ (timePolynomial s b arity labels edges codec closed base).eval
        ((RawPortQuery.encoding s b arity).encode x).length ∧
      StackProtocol.RunsExactly (machine s b arity labels edges codec closed base).computer.step
        (Turing.initList (machine s b arity labels edges codec closed base).computer
          ((RawPortQuery.encoding s b arity).encode x))
        (Turing.haltList (machine s b arity labels edges codec closed base).computer out) time := by
  let w := prepareComputes s b arity labels edges codec closed base
  obtain ⟨t,ht,hr⟩ := Traversal.clean_execute_input_bound h (by rw [rows_length]; exact hn)
  have run := Machine.compose_run w.machine Traversal.preparedMachine _ _ _
    (w.outputs x).steps t (w.outputs x).evals_in_steps hr
  refine ⟨t+(2*((prepared s b arity labels edges codec closed base x).length+1)+(w.outputs x).steps),?_,run⟩
  have hb := w.outputBound.length_le x
  have hw := (w.outputs x).steps_le_m
  have hm := natPolynomial_eval_mono (8*Polynomial.X^2+20*Polynomial.X+12 : Polynomial ℕ) hb
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_X] at hm
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_X]
  unfold Traversal.inputTimeBound at ht
  change t ≤ 8*(prepared s b arity labels edges codec closed base x).length*
    (prepared s b arity labels edges codec closed base x).length+
      18*(prepared s b arity labels edges codec closed base x).length+10 at ht
  dsimp only [Frame.wordEncoding, id_eq] at hm
  change _ ≤ w.time.eval _ + (8 * w.outputBound.bound.eval _ ^ 2 + 20 * w.outputBound.bound.eval _ + 12)
  nlinarith

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.ActionTableCompiler
