import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphListCompiler
import Holant.Complexity.FixedFieldMachines.StackEvaluatorBridge

/-! Physical raw graph compilation followed by the actual finite-field
interpreter. The sole compiler semantic bridge is isolated here for downstream
instantiation by its original-graph theorem; it is not a source hypothesis. -/
namespace Holant.Complexity.FixedFieldMachines.RawGraphEvaluator
open Turing Computability BinaryCompose Holant.Algebraic
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.Complexity.ExactSignatureTables
open Holant.Complexity.GraphPreprocessing.OriginalCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ→ℕ}

 def CompilerCorrect (s b : ℕ) (arity : ℕ→ℕ) : Prop :=
  ∀x : GraphListCompiler.Input s b arity,GraphListCompiler.value x=x.val.labelledGraphCode x.property

 def network (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ)
    (x : GraphListCompiler.Input s b arity) : Holant.Network K 0 :=
  x.val.realize x.property (fun i w=>F.decode (coeff (.inl ⟨i,w⟩)))
    (fun i a b=>F.decode (coeff (.inr (i,a,b))))

 def value (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ)
    (x : GraphListCompiler.Input s b arity) : K := (network F coeff x).denote Fin.elim0

 def Valid (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ)
    (x : GraphListCompiler.Input s b arity) : Prop :=
  (∀v,Signature.OneHot ((network F coeff x).vertex v)) ∧
    (∀e,(network F coeff x).edge e=Signature.disequality)

 abbrev Input (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ) :=
  {x : GraphListCompiler.Input s b arity // Valid F coeff x}

 def inputEncoding (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ) :
    Encoding (Input F coeff) Bool := by
  classical
  exact {
    encode x:=(RawClosedNetwork.validatedEncoding s b arity).encode x.val
    decode bits:=do
      let x←(RawClosedNetwork.validatedEncoding s b arity).decode bits
      if h:Valid F coeff x then some ⟨x,h⟩ else none
    decode_encode x:=by simp [x.property] }

 def machine (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ) : BinaryCompose.Machine :=
  (GraphListCompiler.machine s b arity).compose (StackEvaluatorBridge.machine F coeff)

 def timePolynomial (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ) : Polynomial ℕ :=
  (GraphListCompiler.computes s b arity).time+
    2*((GraphListCompiler.computes s b arity).outputBound.bound+1)+
    StackEvaluatorBridge.runtimePolynomial F coeff

 theorem execute_of_compiler_correct (hc : CompilerCorrect s b arity)
    (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ)
    (x : GraphListCompiler.Input s b arity) (hv : Valid F coeff x) :
    ∃time,time≤(timePolynomial F coeff).eval (RawClosedNetwork.encoding.encode x.val).length ∧
      Kernels.Executes (machine F coeff) (RawClosedNetwork.encoding.encode x.val)
        (F.encoding.encode (value F coeff x)) time := by
  let w:=GraphListCompiler.computes s b arity
  obtain ⟨⟨compileTime,hrun⟩,htime⟩:=w.outputs x
  change Kernels.Executes w.machine
    ((RawClosedNetwork.validatedEncoding s b arity).encode x)
    ((codeEncoding (treeLabelEncoding s b arity)).encode (GraphListCompiler.value x)) compileTime at hrun
  have he:=hc x
  rw [he] at hrun
  obtain ⟨t,ht,heval⟩:=StackEvaluatorBridge.evaluate_graph_code F coeff x.val x.property hv.1 hv.2
  let middle:=(codeEncoding (treeLabelEncoding s b arity)).encode (x.val.labelledGraphCode x.property)
  have hsize:=w.outputBound.length_le x
  rw [he] at hsize
  refine ⟨t+(2*(middle.length+1)+compileTime),?_,?_⟩
  · change t+(2*(middle.length+1)+compileTime)≤_
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_one]
    change middle.length≤w.outputBound.bound.eval (RawClosedNetwork.encoding.encode x.val).length at hsize
    change compileTime≤w.time.eval (RawClosedNetwork.encoding.encode x.val).length at htime
    dsimp [w] at htime hsize
    omega
  · exact BinaryCompose.Machine.compose_run _ _ _ _ _ _ _ hrun heval

 def computes_of_compiler_correct (hc : CompilerCorrect s b arity)
    (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ) :
    Computes (inputEncoding F coeff) F.encoding (fun x=>value F coeff x.val) where
  machine:=machine F coeff
  time:=timePolynomial F coeff
  outputs x:={
    steps:=Classical.choose (execute_of_compiler_correct hc F coeff x.val x.property)
    evals_in_steps:=(Classical.choose_spec (execute_of_compiler_correct hc F coeff x.val x.property)).2
    steps_le_m:=(Classical.choose_spec (execute_of_compiler_correct hc F coeff x.val x.property)).1 }

 theorem inFP_of_compiler_correct (hc : CompilerCorrect s b arity)
    (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ) :
    InFP (inputEncoding F coeff) F.encoding (fun x=>value F coeff x.val) :=
  (computes_of_compiler_correct hc F coeff).inFP

 def primitivePolynomial (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ) : Polynomial ℕ :=
  timePolynomial F coeff*Polynomial.C (machine F coeff).primitiveBudget

 theorem execute_with_primitive_cost_of_compiler_correct (hc : CompilerCorrect s b arity)
    (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ)
    (x : GraphListCompiler.Input s b arity) (hv : Valid F coeff x) :
    ∃time,time≤(timePolynomial F coeff).eval (RawClosedNetwork.encoding.encode x.val).length ∧
      Kernels.Executes (machine F coeff) (RawClosedNetwork.encoding.encode x.val)
        (F.encoding.encode (value F coeff x)) time ∧
      primitiveCost (machine F coeff) time
        (some (initList (machine F coeff).computer (RawClosedNetwork.encoding.encode x.val)))≤
        (primitivePolynomial F coeff).eval (RawClosedNetwork.encoding.encode x.val).length := by
  obtain ⟨t,ht,hr⟩:=execute_of_compiler_correct hc F coeff x hv
  refine ⟨t,ht,hr,?_⟩
  exact (primitiveCost_le _ _ _).trans (by
    simpa [primitivePolynomial] using Nat.mul_le_mul_right (machine F coeff).primitiveBudget ht)

 theorem arithmetic_bound (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ)
    (x : GraphListCompiler.Input s b arity) (hv : Valid F coeff x) :
    (network F coeff x).computedOneHotProgram.run.1=value F coeff x ∧
      (network F coeff x).computedOneHotProgram.run.2≤
        11*((network F coeff x).shape.vertices+(network F coeff x).shape.edges) :=
  (network F coeff x).computedOneHotProgram_spec hv.1 hv.2

end
end Holant.Complexity.FixedFieldMachines.RawGraphEvaluator
