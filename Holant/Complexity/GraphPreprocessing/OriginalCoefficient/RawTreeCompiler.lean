import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionEntry
import Holant.OneHot.StackProgram.GraphCodeMachine.FromRows

/-! Actual raw graph/root entry, original-ID table expansion and closed-tree
bytecode compilation in one finite machine. The semantic expansion premise is
stated explicitly for the component-transport theorem to discharge; neither a
tree nor a size certificate is supplied to a running instruction. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawTreeCompiler
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s b : ℕ) (arity : ℕ → ℕ)
abbrev labelEncoding := treeLabelEncoding s b arity
def bound := Finset.univ.sup (fun a : RawClosedNetwork.TreeLabel s b arity => ((labelEncoding s b arity).encode a).length)
theorem label_length_le (a : RawClosedNetwork.TreeLabel s b arity) :
    ((labelEncoding s b arity).encode a).length≤bound s b arity :=
  Finset.le_sup (f := fun a : RawClosedNetwork.TreeLabel s b arity => ((labelEncoding s b arity).encode a).length) (Finset.mem_univ a)
abbrev machine : Machine := (RawActionEntry.machine s b arity).compose (GraphCodeMachine.FromRows.machine (labelEncoding s b arity) (bound s b arity))
noncomputable def timePolynomial : Polynomial ℕ := RawActionEntry.timePolynomial s b arity+
  ((GraphCodeMachine.FromRows.timePolynomial (bound s b arity))+2*Polynomial.X+2).comp (RawActionEntry.sizePolynomial s b arity)

theorem closed_execute (x : RawRootReach.Input s b arity) (a : RawClosedNetwork.TreeLabel s b arity)
    (ts : Forest (RawClosedNetwork.TreeLabel s b arity)) (count : ℕ)
    (h : Traversal.Expands (RawActionTable.value x.1) (Traversal.reference x.2.val)
      ((GraphCodeMachine.closedEncoding (labelEncoding s b arity)).encode (a,ts)) count)
    (hc : count≤x.1.val.vertices.length) :
    ∃ time, time≤(timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length ∧
      RunsExactly (machine s b arity).computer.step
        (initList (machine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x))
        (haltList (machine s b arity).computer ((codeEncoding (labelEncoding s b arity)).encode (compileClosed a ts))) time := by
  have first := RawActionEntry.timed x
  obtain ⟨n,hn,last⟩ := GraphCodeMachine.FromRows.closed_exact (labelEncoding s b arity) (bound s b arity)
    (label_length_le s b arity) (RawActionTable.value x.1) (Traversal.reference x.2.val) a ts count h
    (by simpa using hc)
  have run := Machine.compose_run (RawActionEntry.machine s b arity)
    (GraphCodeMachine.FromRows.machine (labelEncoding s b arity) (bound s b arity))
    _ (RawActionEntry.value x) _ first.steps n first.evals_in_steps last
  refine ⟨n+(2*((RawActionEntry.value x).length+1)+first.steps),?_,run⟩
  have hi := RawActionEntry.output_length x
  have hm := natPolynomial_eval_mono (GraphCodeMachine.FromRows.timePolynomial (bound s b arity)) hi
  have hs := first.steps_le_m
  change n≤(GraphCodeMachine.FromRows.timePolynomial (bound s b arity)).eval (RawActionEntry.value x).length at hn
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial s b arity*Polynomial.C (machine s b arity).primitiveBudget
theorem closed_primitive (x : RawRootReach.Input s b arity) (a : RawClosedNetwork.TreeLabel s b arity)
    (ts : Forest (RawClosedNetwork.TreeLabel s b arity)) (count : ℕ)
    (h : Traversal.Expands (RawActionTable.value x.1) (Traversal.reference x.2.val)
      ((GraphCodeMachine.closedEncoding (labelEncoding s b arity)).encode (a,ts)) count)
    (hc : count≤x.1.val.vertices.length) :
    ∃ time, time≤(timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length ∧
      RunsExactly (machine s b arity).computer.step
        (initList (machine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x))
        (haltList (machine s b arity).computer ((codeEncoding (labelEncoding s b arity)).encode (compileClosed a ts))) time ∧
      primitiveCost (machine s b arity) time
        (some (initList (machine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x))) ≤
        (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  obtain ⟨n,hn,run⟩ := closed_execute s b arity x a ts count h hc
  refine ⟨n,hn,run,?_⟩
  have ht := Nat.mul_le_mul_right (machine s b arity).primitiveBudget hn
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) ht
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawTreeCompiler
