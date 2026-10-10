import Holant.Complexity.BinaryInterpolation.Chains.Template
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Algebraic.FixedField

/-! Original-labelled native graph data, independent of interpolation sources. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetSource
open Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature K (a i.val))
structure Output (n : ℕ) where
  network : Network K n
  labels : Labelling network.shape s 1 a
  exact : LabelledNetwork.Exact H network labels
  native : ∀e,network.edge e=Signature.disequality
abbrev Output.template {n : ℕ} (N : Output H n):=N.labels.template

theorem template_exact {n : ℕ} (N : Output H n) :
    (N.template.network N.labels.wellFormed H (fun _ : Fin 1=>Signature.disequality)).denote=
      N.network.denote :=
  N.labels.denote_template_of_labels H (fun _ : Fin 1=>Signature.disequality)
    N.network.vertex N.network.edge (fun v x=>
      Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
        (H (N.labels.vertex v)) (N.network.vertex v) (N.exact v)
        (N.labels.vertex_arity v) x)
    (fun e x y=>congrFun₂ (N.native e).symm x y)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetSource
end
