import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionEntry
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawTreeCompiler
import Holant.OneHot.StackProgram.GraphCodeMachine.FromRows

/-! Actual raw graph/root entry, original-ID table expansion and closed-tree
bytecode compilation in one finite machine. The semantic expansion premise is
stated explicitly for the component-transport theorem to discharge; neither a
tree nor a size certificate is supplied to a running instruction. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualTreeCompiler
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1500000
variable (s b : ℕ) (arity : ℕ → ℕ)
abbrev labelEncoding := RawTreeCompiler.labelEncoding s b arity
abbrev bound := RawTreeCompiler.bound s b arity
theorem label_length_le (c : RawClosedNetwork.TreeLabel s b arity) :
    ((labelEncoding s b arity).encode c).length≤bound s b arity := RawTreeCompiler.label_length_le s b arity c
variable (cutA cutZ : Bool)
abbrev machine : Machine := (ResidualActionEntry.machine cutA cutZ s b arity).compose (GraphCodeMachine.FromRows.machine (labelEncoding s b arity) (bound s b arity))
noncomputable def timePolynomial : Polynomial ℕ := ResidualActionEntry.timePolynomial cutA cutZ s b arity+
  ((GraphCodeMachine.FromRows.timePolynomial (bound s b arity))+2*Polynomial.X+2).comp (ResidualActionEntry.sizePolynomial s b arity)

theorem closed_execute (x : ResidualContext.Query s b arity) (a : RawClosedNetwork.TreeLabel s b arity)
    (ts : Forest (RawClosedNetwork.TreeLabel s b arity)) (count : ℕ)
    (h : Traversal.Expands (ResidualActionTable.value cutA cutZ x.1) (Traversal.reference x.2.val)
      ((GraphCodeMachine.closedEncoding (labelEncoding s b arity)).encode (a,ts)) count)
    (hc : count≤(ResidualContext.source x.1).val.vertices.length) :
    ∃ time, time≤(timePolynomial s b arity cutA cutZ).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length ∧
      RunsExactly (machine s b arity cutA cutZ).computer.step
        (initList (machine s b arity cutA cutZ).computer ((ResidualContext.queryEncoding s b arity).encode x))
        (haltList (machine s b arity cutA cutZ).computer ((codeEncoding (labelEncoding s b arity)).encode (compileClosed a ts))) time := by
  have first := ResidualActionEntry.timed cutA cutZ x
  obtain ⟨n,hn,last⟩ := GraphCodeMachine.FromRows.closed_exact (labelEncoding s b arity) (bound s b arity)
    (label_length_le s b arity) (ResidualActionTable.value cutA cutZ x.1) (Traversal.reference x.2.val) a ts count h
    (by simpa using hc)
  have run := Machine.compose_run (ResidualActionEntry.machine cutA cutZ s b arity)
    (GraphCodeMachine.FromRows.machine (labelEncoding s b arity) (bound s b arity))
    _ (ResidualActionEntry.value cutA cutZ x) _ first.steps n first.evals_in_steps last
  refine ⟨n+(2*((ResidualActionEntry.value cutA cutZ x).length+1)+first.steps),?_,run⟩
  have hi := ResidualActionEntry.output_length cutA cutZ x
  have hm := natPolynomial_eval_mono (GraphCodeMachine.FromRows.timePolynomial (bound s b arity)) hi
  have hs := first.steps_le_m
  change n≤(GraphCodeMachine.FromRows.timePolynomial (bound s b arity)).eval (ResidualActionEntry.value cutA cutZ x).length at hn
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial s b arity cutA cutZ*Polynomial.C (machine s b arity cutA cutZ).primitiveBudget
theorem closed_primitive (x : ResidualContext.Query s b arity) (a : RawClosedNetwork.TreeLabel s b arity)
    (ts : Forest (RawClosedNetwork.TreeLabel s b arity)) (count : ℕ)
    (h : Traversal.Expands (ResidualActionTable.value cutA cutZ x.1) (Traversal.reference x.2.val)
      ((GraphCodeMachine.closedEncoding (labelEncoding s b arity)).encode (a,ts)) count)
    (hc : count≤(ResidualContext.source x.1).val.vertices.length) :
    ∃ time, time≤(timePolynomial s b arity cutA cutZ).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length ∧
      RunsExactly (machine s b arity cutA cutZ).computer.step
        (initList (machine s b arity cutA cutZ).computer ((ResidualContext.queryEncoding s b arity).encode x))
        (haltList (machine s b arity cutA cutZ).computer ((codeEncoding (labelEncoding s b arity)).encode (compileClosed a ts))) time ∧
      primitiveCost (machine s b arity cutA cutZ) time
        (some (initList (machine s b arity cutA cutZ).computer ((ResidualContext.queryEncoding s b arity).encode x))) ≤
        (primitivePolynomial s b arity cutA cutZ).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length := by
  obtain ⟨n,hn,run⟩ := closed_execute s b arity cutA cutZ x a ts count h hc
  refine ⟨n,hn,run,?_⟩
  have ht := Nat.mul_le_mul_right (machine s b arity cutA cutZ).primitiveBudget hn
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) ht
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualTreeCompiler
