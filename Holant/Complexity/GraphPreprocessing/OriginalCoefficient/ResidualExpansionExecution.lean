import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualTreeCompiler

/-! Actual finite-machine compilation with the expansion premise discharged
from original graph/cut/root data and computed canonical residual rows. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option Elab.async false
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
open CanonicalStability CanonicalExpansion
variable {s b : ℕ} {arity : ℕ → ℕ}

/-- No prepared tree, expansion witness or count bound is assumed. The machine
reads the original raw graph, the original cut ID and the original root ID. -/
 theorem execute (a z : Bool) (x : ResidualContext.Input s b arity)
    (root : Fin (ResidualContext.source x).val.vertices.length)
    (hr : (network x).incidenceGraph.label root = root) :
    ∃ time, time ≤ (ResidualTreeCompiler.timePolynomial s b arity a z).eval
        (RawClosedNetwork.encoding.encode (ResidualContext.source x).val).length ∧
      RunsExactly (ResidualTreeCompiler.machine s b arity a z).computer.step
        (initList (ResidualTreeCompiler.machine s b arity a z).computer
          ((ResidualContext.queryEncoding s b arity).encode ⟨x,root⟩))
        (haltList (ResidualTreeCompiler.machine s b arity a z).computer
          ((codeEncoding (treeLabelEncoding s b arity)).encode
            (computedTreeCode (component a z x root) none
              (componentRoot (residual a z x) (rootIndex a z x root))
              (component_connected (residual a z x) (rootIndex a z x root))))) time ∧
      primitiveCost (ResidualTreeCompiler.machine s b arity a z) time
        (some (initList (ResidualTreeCompiler.machine s b arity a z).computer
          ((ResidualContext.queryEncoding s b arity).encode ⟨x,root⟩))) ≤
        (ResidualTreeCompiler.primitivePolynomial s b arity a z).eval
          (RawClosedNetwork.encoding.encode (ResidualContext.source x).val).length := by
  have hc := closed a z x root hr
  have run := ResidualTreeCompiler.closed_primitive s b arity a z ⟨x,root⟩
    (closedParts (treeValue a z x root)).1 (closedParts (treeValue a z x root)).2
    (component a z x root).shape.vertices hc.1 hc.2
  rw [code] at run
  exact run

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualExpansion
