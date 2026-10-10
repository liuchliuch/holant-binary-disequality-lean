import Holant.Complexity.FixedFieldMachines.RawGraphEvaluator.FiniteFamily
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.GraphCodeCorrectness

/-! Source Lemma2.18: original closed one-hot native-X networks have a linear
field-operation algorithm and a genuine raw-input polynomial-bit-time machine.
The coefficient field is derived from the fixed finite algebraic family. -/
namespace Holant.Complexity.FixedFieldMachines.RawGraphEvaluator
open Turing Computability BinaryCompose Holant.Algebraic
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open Holant.Complexity.ExactSignatureTables
open Holant.Complexity.GraphPreprocessing.OriginalCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ→ℕ}

 theorem compiler_correct : CompilerCorrect s b arity := GraphCodeCorrectness.value

 def computes (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ) :
    Computes (inputEncoding F coeff) F.encoding (fun x=>value F coeff x.val) :=
  computes_of_compiler_correct compiler_correct F coeff

 theorem raw_graph_inFP (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ) :
    InFP (inputEncoding F coeff) F.encoding (fun x=>value F coeff x.val) :=
  (computes F coeff).inFP

 theorem raw_graph_execute (F : FixedField K n) (coeff : CoefficientIndex s b arity→Fin n→ℚ)
    (x : GraphListCompiler.Input s b arity) (hv : Valid F coeff x) :
    ∃time,time≤(timePolynomial F coeff).eval (RawClosedNetwork.encoding.encode x.val).length ∧
      Kernels.Executes (machine F coeff) (RawClosedNetwork.encoding.encode x.val)
        (F.encoding.encode (value F coeff x)) time ∧
      primitiveCost (machine F coeff) time
        (some (initList (machine F coeff).computer (RawClosedNetwork.encoding.encode x.val)))≤
        (primitivePolynomial F coeff).eval (RawClosedNetwork.encoding.encode x.val).length :=
  execute_with_primitive_cost_of_compiler_correct compiler_correct F coeff x hv

/-- Original finite algebraic coefficients, original ordered raw graph, actual
fixed Boolean-stack machine, unchanged faithful field answer, linear arithmetic
count and polynomial transition/primitive counts. All connectivity, roots,
parents, cuts, code and field coordinates are derived, never supplied by input. -/
 theorem source_one_hot_matching_evaluation
    (coeff : CoefficientIndex s b arity→K) (halg : ∀a,IsAlgebraic ℚ (coeff a))
    (x : GraphListCompiler.Input s b arity)
    (hf : ∀v,Signature.OneHot ((ambientNetwork coeff x).vertex v))
    (hX : ∀e,(ambientNetwork coeff x).edge e=Signature.disequality) :
    let F:=familyPresentation coeff halg
    let cs:=familyCoordinates coeff halg
    ((((network F cs x).computedOneHotProgram.run.1 : familyField coeff):K)=
      (ambientNetwork coeff x).denote Fin.elim0 ∧
      (network F cs x).computedOneHotProgram.run.2≤11*(x.val.vertices.length+x.val.edges.length)) ∧
    ∃time,∃answer : familyField coeff,
      (answer:K)=(ambientNetwork coeff x).denote Fin.elim0 ∧
      time≤(timePolynomial F cs).eval (RawClosedNetwork.encoding.encode x.val).length ∧
      Kernels.Executes (machine F cs) (RawClosedNetwork.encoding.encode x.val)
        (F.encoding.encode answer) time ∧
      primitiveCost (machine F cs) time
        (some (initList (machine F cs).computer (RawClosedNetwork.encoding.encode x.val)))≤
        (primitivePolynomial F cs).eval (RawClosedNetwork.encoding.encode x.val).length := by
  exact ⟨finite_family_arithmetic_bound coeff halg x hf hX,
    finite_family_evaluate_of_compiler_correct compiler_correct coeff halg x hf hX⟩

end
end Holant.Complexity.FixedFieldMachines.RawGraphEvaluator
