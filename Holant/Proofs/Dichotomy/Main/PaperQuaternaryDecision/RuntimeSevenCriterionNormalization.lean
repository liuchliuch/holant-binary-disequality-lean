import Holant.Proofs.Recognition.RuntimeSevenCriterionNormalization

/-! Exact seven-clause normalization for forward K on the original family.
The native support table is the original table because K inverse cancels K. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSevenCriterionNormalization
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : Fin s→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i))
def family : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin s => (⟨arity i,G i⟩ : AnySignature AlgebraicComplex))
def Profile := (i : Fin s) → Fin (arity i+1)
def layers (p : Profile (s:=s) (arity:=arity)) (i : Fin s) : ℕ := (p i).val
def completedArity (p : Profile (s:=s) (arity:=arity)) (i : Fin s) : ℕ :=
  arity i+Holant.LocalDrafts.Hardness.SingleWeightCompletion.extra (arity i) (layers p i)
def completed (p : Profile (s:=s) (arity:=arity)) (i : Fin s) : Signature AlgebraicComplex (completedArity p i) :=
  Holant.LocalDrafts.Hardness.SingleWeightCompletion.completed (G i) (layers p i)

def forward (i : Fin s) := sourceKBasis.action (G i)
abbrev native := G
def central (i : Fin s) := Signature.centralRestriction (G i)

theorem family_forward : family (forward G)=familyAction sourceKBasis (family G) := by
  exact Set.range_comp' (fun f : AnySignature AlgebraicComplex=>(⟨f.1,sourceKBasis.action f.2⟩ : AnySignature AlgebraicComplex))
    (fun i : Fin s=>(⟨arity i,G i⟩ : AnySignature AlgebraicComplex))

theorem native_forward :
    Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.native (forward G)=G := by
  funext i
  exact InvertibleKernel.symm_action_action sourceKBasis (G i)


theorem native_forward_apply (i : Fin s) :
    Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.native (forward G) i=G i :=
  InvertibleKernel.symm_action_action sourceKBasis (G i)

theorem central_forward :
    Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.central (forward G)=central G := by
  funext i
  simp only [Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.central,
    native_forward_apply,central]

theorem oneSided_iff : OneSidedAlternative (preprocess (family (forward G))) ↔
    CommonOneSided (family (native G)) ∧ EOTract (preprocess (family (central G))) := by
  have h := Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.oneSided_iff (forward G)
  simpa only [native_forward,native_forward_apply,central_forward,native,family,Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.family] using h

theorem singleWeight_iff : SingleWeightAlternative (preprocess (family (forward G))) ↔
    BothChargeSigns (family (native G)) ∧
      ∃p : Profile (s:=s) (arity:=arity),
        (∀i,Signature.SingleLayer (native G i) (layers p i)) ∧
        EOTract (preprocess (family (completed (native G) p))) := by
  simpa only [native_forward,native_forward_apply,native,family,Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.family,
    Profile,Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.Profile,layers,Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.layers,
    completed,Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.completed,completedArity,Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.completedArity] using
    Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.singleWeight_iff (forward G)

theorem tract_iff : Tract (family (forward G)) ↔
    OneSidedAlternative (preprocess (family (forward G))) ∨
      SingleWeightAlternative (preprocess (family (forward G))) ∨
      MatchingAlternative (family (forward G)) ∨ TractX (family (forward G)) :=
  Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization.tract_iff (forward G)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSevenCriterionNormalization
end
