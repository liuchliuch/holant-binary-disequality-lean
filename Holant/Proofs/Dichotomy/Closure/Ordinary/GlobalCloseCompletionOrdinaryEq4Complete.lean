import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralComplete
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2PrimeCurrent
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicLift

/-! Any actual ordinary Eq4 graph on the complete retained dictionary now
has an unconditional whole-current common-basis or original-G hardness exit.
The negative source is selected internally, with literal pins and Z. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOrdinaryEq4Complete
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace O
export GlobalCloseCompletionStopOrdinarySource (family table tract_iff_current)
end O
namespace E
export GlobalCloseCompletionC2PrimeCurrent (data old_included z_member)
export GlobalCloseCompletionC2OrdinaryPairOutcome (HasEq4)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (P : Palette G) (anchor : E.HasEq4 (O.table G P))

include anchor in
theorem classified : Tract (O.family G P) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  let src:=E.data G P anchor
  by_cases tract : Tract (GenericOrdinarySource.family G src)
  · exact Or.inl (tract.mono_family (E.old_included G P anchor))
  · right
    obtain ⟨z,literal⟩:=GlobalCloseCompletionUnaryIsotropicLift.z_exists src.K src.H (E.z_member G P anchor)
    have exactZ : (⟨src.b z.val,src.H z⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩ := by
      refine literal.trans ?_
      apply congrArg (fun f : Signature src.K 2=>(⟨2,f⟩ : AnySignature src.K))
      funext x
      cases h0 : x 0 <;> cases h1 : x 1 <;> rfl
    exact NoXGeneralComplete.countingHard G src z exactZ ((GenericOrdinarySource.rejected_iff G src).mp tract)

include anchor in
theorem current_classified :
    TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P)) ∨
      NoXWeightedAntiResourcesOriginal.Hard G := by
  rcases classified G P anchor with tract|hard
  · exact Or.inl ((O.tract_iff_current G P).mp tract)
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOrdinaryEq4Complete
end
