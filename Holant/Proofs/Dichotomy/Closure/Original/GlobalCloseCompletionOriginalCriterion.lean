import Holant.Proofs.Dichotomy.Closure.Engine.GlobalCloseCompletionEngineTransitions
import Holant.Proofs.Algorithms.BinaryDisequalityTractability

/-! The current common-basis criterion implies the exact original input
criterion, including zero and nullary rows via its prescribed preprocessing.
No original coefficient, label, or native equality anchor is replaced. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOriginalCriterion
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace B
export BinaryDisequalityTractability (retainedFamily retained_finite)
end B
namespace O
export Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput
  (retains_preprocessed_original retains_identity)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G

theorem included : preprocess (B.retainedFamily G)⊆CurrentFrontierClosure.currentFamily G (Initial.palette G) := by
  rintro f ⟨member,positive,nonzero⟩
  rcases member with original|identity
  · obtain ⟨g,hg,he⟩:=O.retains_preprocessed_original G f original positive nonzero
    refine ⟨g,?_,he⟩
    rwa [Initial.family_exact]
  · have hf : f=⟨2,kernelSignature Signature.equality⟩:=Set.mem_singleton_iff.mp identity
    subst f
    refine ⟨⟨2,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature⟩,?_,?_⟩
    · rw [Initial.family_exact]
      exact O.retains_identity G
    · apply congrArg (fun q : Signature AlgebraicComplex 2=>(⟨2,q⟩ : AnySignature AlgebraicComplex))
      funext x
      cases h0 : x 0 <;> cases h1 : x 1 <;>
        simp [FrontierCommonPresentation.embed,
          Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature,
          kernelSignature,Signature.equality,h0,h1]

theorem of_current (criterion : GlobalCloseCompletionEngineTransitions.CurrentTract G (Initial.palette G)) :
    TractX (familyAction sourceKBasis (B.retainedFamily G)) := by
  have sub : preprocess (familyAction sourceKBasis (B.retainedFamily G))⊆
      preprocess (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G (Initial.palette G))) := by
    rw [Conformal.preprocess_familyAction]
    rintro f ⟨g,hg,rfl⟩
    refine ⟨⟨g,included G hg,rfl⟩,hg.2.1,?_⟩
    exact fun zero=>hg.2.2 ((Conformal.action_eq_zero_iff sourceKBasis g.2).mp zero)
  refine ⟨criterion.1.subset sub,?_⟩
  rcases criterion.2 with small|affine|product|localAffine
  · exact Or.inl (small.mono_family sub)
  · exact Or.inr (Or.inl (affine.mono_family sub))
  · exact Or.inr (Or.inr (Or.inl (product.mono_family sub)))
  · exact Or.inr (Or.inr (Or.inr (localAffine.mono_family sub)))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOriginalCriterion
end
