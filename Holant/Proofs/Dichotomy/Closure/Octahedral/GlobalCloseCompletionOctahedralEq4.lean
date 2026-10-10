import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralEndpointCurrent
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Graph

/-! The actual dd terminal is converted to the existing literal Eq4 graph
contract over the same original-field palette. Its scalar is its real first
entry, and its entire realization is serialized with its original labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralEq4
open Holant Holant.Algebraic Holant.Tractable Holant.Complexity
open Holant.Complexity.FixedGadgetSubstitution
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open GlobalCloseCompletionOctahedralGeometry
namespace E
export GlobalCloseCompletionOctahedralEndpointCurrent (Output)
end E
namespace D
export GlobalCloseCompletionOctahedralDressing (ψ)
end D
namespace T
export GlobalCloseCompletionOctahedralTerminals (target)
end T
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)

theorem target_zero : T.target 0=(Holant.EightVertex.ProductAnchor.equalityFour : Signature ℂ 4) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.target,RankTwo.BaseTerminals.terminalShape,RankTwo.literalEquality,
      Holant.EightVertex.ProductAnchor.equalityFour,funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

variable (output : E.Output G P tau) (dd : output.form=0)

include dd in
theorem original_eq4 : output.tensor.table=output.tensor.table (fun _=>false) •
    Holant.EightVertex.ProductAnchor.equalityFour := by
  have h := output.coefficients
  rw [dd,target_zero] at h
  have hscale : D.ψ G (output.tensor.table (fun _=>false))=output.scalar := by
    have he := congrFun h (fun _=>false)
    simpa [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour] using he
  funext x
  apply (D.ψ G).injective
  change RingHomRealization.mapSignature (D.ψ G) output.tensor.table x=_
  rw [h]
  simp only [Pi.smul_apply,smul_eq_mul,map_mul,hscale]
  congr 1
  simp [Holant.EightVertex.ProductAnchor.equalityFour]

include output dd in
theorem source : Nonempty (GlobalCloseCompletionEq4Graph.Output G P) := by
  obtain ⟨N,uses,native,denote⟩ := Holant.OpenNetworkComposition.OrdinaryNormalization.realizes_exists_ordinary
    (P.retainsIdentity G) output.tensor.actual
  change ∀v,∃i : Fin P.count,(⟨P.arity i.val,P.table i⟩ : AnySignature (OI.K G))=
    ⟨N.shape.arity v,N.vertex v⟩ at uses
  let labels : Labelling N.shape P.count 1 P.arity := {
    vertex := fun v=>(uses v).choose
    vertex_arity := fun v=>congrArg Sigma.fst (uses v).choose_spec
    edge := fun _=>0 }
  have nonzero : output.tensor.table (fun _=>false)≠0 := by
    intro hz
    apply output.endpoint.1
    change (ClosureSourceRows.embedding G) (output.tensor.table (fun _=>false))=0
    rw [hz,map_zero]
  exact ⟨⟨N,labels,fun v=>(uses v).choose_spec,native,
    output.tensor.table (fun _=>false),nonzero,
    denote.trans (original_eq4 G P tau output dd)⟩⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralEq4
end
