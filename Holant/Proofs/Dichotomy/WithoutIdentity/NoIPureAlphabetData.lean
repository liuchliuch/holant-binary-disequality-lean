import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePinsData

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureAlphabetData
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)
structure Data extends NoIPurePinsData.Data L H F where
  equality : Fin count
  equality_literal : (⟨arity equality.val,table equality⟩ : AnySignature K)=
    ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩
  flip : Fin count
  flip_literal : (⟨arity flip.val,table flip⟩ : AnySignature K)=
    ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩

section Maps
variable {K : Type} [Field K] (phi : K→+*AlgebraicComplex)
theorem map_injective : Function.Injective (RingHomRealization.mapAny phi) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m:=congrArg Sigma.fst h
  subst m
  have hf:=eq_of_heq (Sigma.mk.inj_iff.mp h).2
  congr 1
  funext x
  apply phi.injective
  exact congrFun hf x

theorem map_eq4 : RingHomRealization.mapAny phi
    (⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ : AnySignature K)=
    ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  unfold RingHomRealization.mapAny
  congr 1
  funext x
  simp [RingHomRealization.mapAny,RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour]

theorem map_x : RingHomRealization.mapAny phi
    (⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩ : AnySignature K)=
    ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩ := by
  unfold RingHomRealization.mapAny
  congr 1
  funext x
  simp [RingHomRealization.mapAny,RingHomRealization.mapSignature,Signature.disequality]
end Maps
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureAlphabetData
end
