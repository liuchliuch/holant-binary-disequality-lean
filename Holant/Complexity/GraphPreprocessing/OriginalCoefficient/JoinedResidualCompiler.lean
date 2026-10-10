import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawComponentInputs
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansionExecution
import Holant.OneHot.StackProgram.GraphCodeMachine.JoinCode

/-! Actual two-branch residual compilation and addition on the selected
original cut. Each branch derives its entire original-ID action table and tree
expansion internally. The code target below names components of the conditioned
original network; literal restriction/conditioning transport is separate. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.JoinedResidualCompiler
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.OneHot.StackProgram.GraphCodeMachine CanonicalStability
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
def branchValue (a z : Bool) (x : RawComponentInputs.CycleInput s b arity) : Code (RawClosedNetwork.TreeLabel s b arity) :=
  computedTreeCode (ResidualExpansion.component a z x.val.1 x.val.2) none
    (componentRoot (ResidualExpansion.residual a z x.val.1) (ResidualExpansion.rootIndex a z x.val.1 x.val.2))
    (component_connected (ResidualExpansion.residual a z x.val.1) (ResidualExpansion.rootIndex a z x.val.1 x.val.2))
theorem branch_run (a z : Bool) (x : RawComponentInputs.CycleInput s b arity) :
    ∃ time, time≤(ResidualTreeCompiler.timePolynomial s b arity a z).eval
        (RawClosedNetwork.encoding.encode (ResidualContext.source x.val.1).val).length ∧
      RunsExactly (ResidualTreeCompiler.machine s b arity a z).computer.step
        (initList (ResidualTreeCompiler.machine s b arity a z).computer ((RawComponentInputs.residualEncoding s b arity).encode x))
        (haltList (ResidualTreeCompiler.machine s b arity a z).computer ((codeEncoding (treeLabelEncoding s b arity)).encode (branchValue a z x))) time := by
  have hr : (ResidualExpansion.network x.val.1).incidenceGraph.label x.val.2=x.val.2 := x.property.1
  obtain ⟨n,hn,run,_⟩ := ResidualExpansion.execute a z x.val.1 x.val.2 hr
  exact ⟨n,hn,run⟩
theorem raw_length_le (x : RawComponentInputs.CycleInput s b arity) :
    (RawClosedNetwork.encoding.encode (ResidualContext.source x.val.1).val).length≤
      ((RawComponentInputs.residualEncoding s b arity).encode x).length := by
  change (RawClosedNetwork.encoding.encode (ResidualContext.source x.val.1).val).length≤
    (Holant.Algebraic.frame (Holant.Algebraic.frame (RawClosedNetwork.encoding.encode (ResidualContext.source x.val.1).val)++
      encodeNat (ResidualContext.edge x.val.1).val)++List.replicate x.val.2.val true).length
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega
noncomputable def branchComputes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawComponentInputs.residualEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) (branchValue a z) where
  machine := ResidualTreeCompiler.machine s b arity a z
  time := ResidualTreeCompiler.timePolynomial s b arity a z
  outputs x := {
    steps := Classical.choose (branch_run a z x)
    evals_in_steps := (Classical.choose_spec (branch_run a z x)).2
    steps_le_m := le_trans (Classical.choose_spec (branch_run a z x)).1
      (natPolynomial_eval_mono _ (raw_length_le x)) }
def value (x : RawComponentInputs.CycleInput s b arity) := addCode (branchValue false true x) (branchValue true false x)
noncomputable def joinComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawComponentInputs.residualEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) value :=
  (pairComputes (branchComputes false true s b arity) (branchComputes true false s b arity)).andThen
    (Join.addComputes (treeLabelEncoding s b arity))
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawComponentInputs.cycleEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) value :=
  (RawComponentInputs.serializeComputes s b arity).andThen (joinComputes s b arity)
abbrev joinMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine (ResidualTreeCompiler.machine s b arity false true) (ResidualTreeCompiler.machine s b arity true false)).compose
    (Join.machine ((codeEncoding (treeLabelEncoding s b arity)).encode [.swap,.add]))
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) := CycleQuery.machine.compose (joinMachine s b arity)
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (RawComponentInputs.cycleEncoding s b arity) (codeEncoding (treeLabelEncoding s b arity)) value := (computes s b arity).inFP
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.JoinedResidualCompiler
