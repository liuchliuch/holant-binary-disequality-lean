import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4PairedSource
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsAnchor
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIAnchorConsumer

/-! The real paired-square spectral resource is consumed on the complete
retained family. Its genuine equality anchor gives a common-family criterion
or controlled hardness of precisely the original native dictionary and field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4PairedConsumer
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace S
export GlobalCloseCompletionComplementQ4Series (row)
end S
namespace E
export GlobalCloseCompletionComplementQ4Source (Extension)
end E
namespace P
export GlobalCloseCompletionComplementQ4PairedSource (Normal)
export GlobalCloseCompletionComplementQ4ClassificationPaired (dense products)
end P
namespace A
export GlobalCloseCompletionUnaryDescentSource (ambient family)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem tractX_mono {F H : SignatureFamily AlgebraicComplex} (subset : F⊆H) (tract : TractX H) :
    TractX F := by
  have sub:=preprocess_mono subset
  refine ⟨tract.1.subset sub,?_⟩
  rcases tract.2 with small|affine|product|localAffine
  · exact Or.inl (small.mono_family sub)
  · exact Or.inr (Or.inl (affine.mono_family sub))
  · exact Or.inr (Or.inr (Or.inl (product.mono_family sub)))
  · exact Or.inr (Or.inr (Or.inr (localAffine.mono_family sub)))

theorem row_even {K : Type} [Field K] (a b c d : K) : EvenSupport (S.row a b c d) := by
  intro x hx
  rw [Holant.EightVertex.ProductAnchor.weight_four] at hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals try norm_num [h0,h1,h2,h3] at hx
  all_goals simp [S.row,table,h0,h1,h2,h3]

variable {size degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin size)→Signature L (arity i.val)) (F : FixedField L degree)

theorem extension_classified (r s : L) (hr : r^2=1) (hs : s^2=1)
    (E : E.Extension H F (S.row (r/2) (1/2) ((s*r)/2) (1/2))) :
    TractX (familyAction sourceKBasis (A.ambient L H)) ∨ (NoISuppliedIdentityConsumer.target L H F).Hard := by
  let q:=S.row (r/2) (1/2) ((s*r)/2) (1/2)
  have actual : Gadget.Realizes (A.family L E.table) .disequality q:=
    Gadget.realizes_of_mem _ .disequality _ ⟨E.label,E.literal⟩
  have anchor:=PaperTerminalBridgeEqualProductsAnchor.source L.subtype (A.family L E.table) q actual
    (row_even _ _ _ _) (P.dense r s hr hs) (P.products r s hr hs)
  have mapped : RingHomRealization.mapFamily L.subtype (A.family L E.table)=A.ambient L E.table := by
    ext f
    constructor
    · rintro ⟨g,⟨i,rfl⟩,rfl⟩;exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩;exact ⟨_,⟨i,rfl⟩,rfl⟩
  rw [mapped] at anchor
  rcases NoIAnchorConsumer.classified L E.table F anchor with positive|hard
  · left
    have retained : A.ambient L H⊆A.ambient L E.table := by
      rintro f ⟨i,rfl⟩
      refine ⟨E.old i,?_⟩
      exact congrArg (RingHomRealization.mapAny L.subtype) (E.old_literal i)
    exact tractX_mono (familyAction_mono sourceKBasis retained) positive
  · right
    exact NoIOrdinaryRaw.Target.Hard.compose
      (S:=NoISuppliedIdentityConsumer.target L E.table F)
      (T:=NoISuppliedIdentityConsumer.target L H F) hard E.source

theorem real_classified {a : L} (P : P.Normal H a) (ha : a≠0) (hr : P.r^2=1) :
    TractX (familyAction sourceKBasis (A.ambient L H)) ∨ (NoISuppliedIdentityConsumer.target L H F).Hard :=
  extension_classified L H F P.r P.s hr P.sign (P.real F ha hr)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4PairedConsumer
end
