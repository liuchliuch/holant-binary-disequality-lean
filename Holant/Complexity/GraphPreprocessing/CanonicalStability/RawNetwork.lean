import Holant.Complexity.GraphPreprocessing.CanonicalStability.EvaluationChildren
import Holant.OneHot.StackProgram.GraphCode
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawParentTable

/-! The original raw parent-table producer and GraphCode use exactly the same
incidence graph, before any component restriction or conditioning is performed. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.GraphPreprocessing.CanonicalStability
open Holant.OneHot.Computable OriginalCoefficient
variable {s b : ℕ} {arity : ℕ → ℕ} (r : Holant.Complexity.RawClosedNetwork)

/-- The literal original lookup graph equals the labelNetwork incidence graph;
this identifies data choices, not merely semantic network values. -/
 theorem labelNetwork_graph (h : r.WellFormed s b arity) :
    (r.labelNetwork h).incidenceGraph = r.graph h := rfl

/-- The physical original parent producer supplies exactly the canonical table
of the network used by computedGraphCode. -/
 theorem raw_parentTable (h : r.WellFormed s b arity) :
    RawParentTable.value ⟨r,h⟩ = (r.labelNetwork h).incidenceGraph.parentTable :=
  (congrArg Graph.parentTable (labelNetwork_graph r h)).symm

/-- Component root enumeration keeps the very same original integer IDs. -/
 theorem raw_roots (h : r.WellFormed s b arity) :
    (r.graph h).roots.map Fin.val = (r.labelNetwork h).incidenceGraph.roots.map Fin.val :=
  (congrArg (fun g : Graph => g.roots.map Fin.val) (labelNetwork_graph r h)).symm

end Holant.Complexity.GraphPreprocessing.CanonicalStability
