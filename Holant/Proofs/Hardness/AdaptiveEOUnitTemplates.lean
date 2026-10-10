import Holant.Proofs.Hardness.AdaptiveEOUnitLabels
import Holant.Proofs.Hardness.AdaptiveEOUnitNative

/-! Exact serialized four-coefficient EO unit macros, retaining the actual original q
index and every unary occurrence and native edge. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.AdaptiveEOUnitTemplates
open Holant Holant.Complexity FixedGadgetSubstitution
open AdaptiveEOUnitLocal AdaptiveEOUnitLabels
variable {K : Type*} [Field K] (q : Signature K 4)

theorem actual (one : Bool) :
    ((template q one).network (template_valid q one) (palette q)
      (fun _ : Fin 1=>Signature.disequality)).denote=(unitNetwork q one).denote := by
  apply Labelling.denote_template_of_labels (labels q one) _ _
    (unitNetwork q one).vertex (unitNetwork q one).edge
  · intro v x
    exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply _ _
      (labels_exact q one v) ((labels q one).vertex_arity v) x
  · intro e x y
    exact congrFun₂ (AdaptiveEOUnitNative.unit_native q one e).symm x y

theorem unit_denote (hq : EOSupport q) (one : Bool) :
    ((template q one).network (template_valid q one) (palette q)
      (fun _ : Fin 1=>Signature.disequality)).denote=scale q one • unit one := by
  rw [actual]
  exact unit_value q hq one

theorem counts (one : Bool) :
    (template q one).vertices.length=8 ∧ (template q one).edges.length=7 := by
  rw [Labelling.vertices_length,Labelling.edges_length]
  exact AdaptiveEOUnitNative.unit_counts q one

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.AdaptiveEOUnitTemplates
