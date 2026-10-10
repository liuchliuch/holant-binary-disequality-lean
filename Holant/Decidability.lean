import Holant.Proofs.Dichotomy.Main.PaperMainTheoremsDecision
import Holant.Proofs.Recognition.RuntimeSevenDecision

/-! Exact algebraic-input recognition. Each theorem quantifies one Turing
machine before all finite family layouts and RootCode inputs. These results
assert decidability; they do not assert polynomial-time recognition. -/
namespace Holant.Decidability
export Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems
  (binaryDisequality_uniform literalEquality_uniform quaternary_uniform)
export Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenDecision
  (uniform_source)
end Holant.Decidability
