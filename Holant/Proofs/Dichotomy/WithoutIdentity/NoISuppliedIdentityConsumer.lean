import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeCriterionReturn
import Holant.Proofs.Dichotomy.Native.NativeTableFieldCodec
import Holant.Proofs.Dichotomy.Main.PaperLiteralEquality

/-! A physically supplied equality is consumed before returning to the exact
old no-I oracle. The common basis and every old family row are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISuppliedIdentityConsumer
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {r degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin r)→Signature L (a i.val)) (F : FixedField L degree)
namespace A
export GlobalCloseCompletionUnaryDescentSource (ambient)
end A

def target : NoIOrdinaryRaw.Target := PaperControlledHardness.target
  (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
  ((NativeAntiTargetSource.base H F).evaluate F)

theorem classified (D : NoISuppliedIdentityData.Data L H F) :
    TractX (familyAction sourceKBasis (A.ambient L H)) ∨ (target L H F).Hard := by
  letI : Algebra ℚ D.K:=D.K.algebra'
  let G:=NativeTableFieldCodec.ambient D.K D.table
  have literal : (⟨D.b D.identity.val,G D.identity⟩ : AnySignature AlgebraicComplex)=
      ⟨2,kernelSignature Signature.equality⟩ := by
    have h:=congrArg (RingHomRealization.mapAny D.K.subtype) D.identity_literal
    change (⟨D.b D.identity.val,G D.identity⟩ : AnySignature AlgebraicComplex)=
      ⟨2,RingHomRealization.mapSignature D.K.subtype (fun x=>Signature.equality (x 0) (x 1))⟩ at h
    rw [h]
    congr 1
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp [RingHomRealization.mapSignature,kernelSignature,Signature.equality,h0,h1]
  rcases PaperLiteralEquality.criterion_or_controlledHard G D.identity literal with positive|hard
  · exact Or.inl (NoINativeCriterionReturn.criterion (A.ambient L H) (A.ambient D.K D.table)
      (Set.finite_range _) (Set.finite_range _) D.basis D.native D.retained positive)
  · apply Or.inr
    exact NoIOrdinaryRaw.Target.Hard.compose (S:=PaperLiteralEqualityHardness.target G)
      (T:=target L H F) hard
      (Programme.compose (NativeTableFieldCodec.controlled D.K D.presentation D.table) D.source)

theorem tract_or_hard (D : NoISuppliedIdentityData.Data L H F) :
    Tract (familyAction sourceKBasis (A.ambient L H)) ∨ (target L H F).Hard :=
  (classified L H F D).imp TractX.tract id

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISuppliedIdentityConsumer
end
