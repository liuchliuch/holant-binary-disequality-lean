import Holant.Proofs.Traversal.ArityTwo.RawCompiler
import Holant.Proofs.Traversal.ArityTwo.Realization
import Holant.Proofs.Traversal.ArityTwo.FixedField


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawFP
open Holant Holant.Complexity Holant.Algebraic Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A K : Type} [Fintype A] [DecidableEq A] [Field K] [Algebra ℚ K] {n : ℕ}
variable (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ) (codec : Encoding A Bool)

abbrev Program (A : Type) := {p : Code A // ∃ cs : List (Component A), p = componentsCode cs}

def programEncoding : Encoding (Program A) Bool := by
  classical
  exact RunComposition.restricted (codeEncoding codec) (fun p => ∃ cs, p = componentsCode cs)

def programValue (p : Program A) : K :=
  ((run (FixedField.coefficients F coords) p.val []).map (fun result => result.1.getD 0 0)).getD 0

theorem programValue_components (cs : List (Component A)) :
    programValue F coords ⟨componentsCode cs,⟨cs,rfl⟩⟩ =
      evaluateComponents (FixedField.coefficients F coords) cs := by
  simp [programValue,run_components]

def programComputes : Computes (programEncoding codec) F.encoding (programValue F coords) where
  machine := FixedField.machine F coords codec
  time := FixedField.runtimePolynomial F coords codec
  outputs p := by
    let cs := Classical.choose p.property
    have hp : p = ⟨componentsCode cs,⟨cs,rfl⟩⟩ := Subtype.ext (Classical.choose_spec p.property)
    rw [hp]
    let run := FixedField.evaluate_components_code F coords codec cs
    let t := Classical.choose run
    have ht := (Classical.choose_spec run).1
    have hr := (Classical.choose_spec run).2
    refine { steps := t, evals_in_steps := ?_, steps_le_m := ht }
    simpa only [programValue_components,programEncoding,RunComposition.restricted,Machine.Kernels.Executes,
      StackProtocol.RunsExactly,Function.flip_def,Option.map_some,bind] using hr

variable (s b : ℕ) (arity : ℕ → ℕ)
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (hd : ∀ i : Fin s, arity i.val ≤ 2)

def compiled (r : RawCompiler.Input s b arity) : Program A :=
  ⟨RawCompiler.code s b arity labels edges r,⟨RawCompiler.descriptors s b arity labels edges r,rfl⟩⟩

def compilerComputes : Computes (RawCompiler.encoding s b arity) (programEncoding codec)
    (compiled s b arity labels edges) :=
  recode (RawCompiler.computes s b arity labels edges codec hd) id (fun _ => rfl) (fun _ => rfl)

def answer (r : RawCompiler.Input s b arity) : K :=
  (r.val.realize r.property (fun i x => F.decode (coords (labels i x)))
    (fun i a b => F.decode (coords (edges i a b)))).denote Fin.elim0

include hd in
theorem compiled_value (r : RawCompiler.Input s b arity) :
    programValue F coords (compiled s b arity labels edges r) = answer F coords s b arity labels edges r := by
  obtain ⟨cs,hc⟩ := Descriptors.all_total r.val r.property
    (RawCompiler.vertex s b arity labels r) (RawCompiler.edge s b arity edges r)
    (fun v => hd (r.val.signatureLabel r.property v))
  have he := labelled_all_correct r.val r.property labels edges (FixedField.coefficients F coords)
    (fun v => hd (r.val.signatureLabel r.property v)) cs hc
  simpa [compiled,RawCompiler.code,RawCompiler.descriptors,hc,programValue,run_components,
    answer,FixedField.coefficients] using he

/-- Compilation, framing/transfer and arithmetic all occur inside this single
finite machine. Its polynomial is in the original faithful raw bit length. -/
def computes : Computes (RawCompiler.encoding s b arity) F.encoding
    (answer F coords s b arity labels edges) :=
  congrComputes ((compilerComputes codec s b arity labels edges hd).andThen
    (programComputes F coords codec)) (compiled_value F coords s b arity labels edges hd)

theorem computes_machine : (computes F coords codec s b arity labels edges hd).machine =
    RawBytecodeMachine.machine s b arity labels edges codec F coords := by
  simp only [computes,congrComputes,RunComposition.andThen_machine,
    compilerComputes,recode,RawCompiler.computes_machine,programComputes,RawBytecodeMachine.machine]

include codec hd in
theorem inFP : InFP (RawCompiler.encoding s b arity) F.encoding (answer F coords s b arity labels edges) :=
  (computes F coords codec s b arity labels edges hd).inFP

theorem primitive_bound (r : RawCompiler.Input s b arity) :
    let w := computes F coords codec s b arity labels edges hd
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes F coords codec s b arity labels edges hd) r

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawFP
