import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorCodec
import Holant.Proofs.Dichotomy.Closure.Generic.GlobalCloseCompletionGenericOrdinaryData
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned

/-! Ordinary finite scalar-Eq4 graphs obtain both computational pins through
one genuine native finite-table anchor and the existing exact pin programme.
Every original ordinary row, including its actual anti weights, is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOrdinaryAnchorPins
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
namespace I
export GlobalCloseCompletionOrdinaryAnchorInput (Input mapped native anchor)
end I
namespace C
export GlobalCloseCompletionOrdinaryAnchorCodec (toOriginal)
end C
namespace B
export GlobalCloseCompletionGenericOrdinaryData (build family_exact transformed_included)
end B
namespace O
export GenericOrdinarySource (field arity table count family)
end O
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (Holant.LocalDrafts.RemoteWork.StableClosureV2.OI.K G) :=
  Holant.LocalDrafts.RemoteWork.StableClosureV2.OI.numberField G
variable (D : I.Input G)
local instance : Algebra ℚ D.K := D.K.algebra'

def data : GenericOrdinarySource.Data G :=
  B.build G (I.native G D) (I.anchor G D) (C.toOriginal G D)

theorem old_included : UniversalPairReduction.FiniteFamily.family (I.mapped G D)⊆
    O.family G (data G D) := by
  rintro f ⟨i,rfl⟩
  have member : (⟨D.b i.val,sourceKBasis.action (I.native G D i)⟩ : AnySignature AlgebraicComplex)∈
      familyAction (I.anchor G D).basis (UniversalPairReduction.FiniteFamily.family (I.native G D)) :=
    ⟨⟨D.b i.val,I.native G D i⟩,⟨i,rfl⟩,rfl⟩
  have h := B.transformed_included G (I.native G D) (I.anchor G D) (C.toOriginal G D) member
  simpa only [data,I.native,KSourceTransport.nativeSignatures,InvertibleKernel.action_symm_action] using h

theorem old_member (i : Fin D.count) :
    (⟨D.b i.val,I.mapped G D i⟩ : AnySignature AlgebraicComplex)∈O.family G (data G D) :=
  old_included G D ⟨i,rfl⟩

private theorem lift_anti {K : Type} [Field K] (phi : K→+*AlgebraicComplex)
    {n : ℕ} (f : Signature K n) (v w : AlgebraicComplex)
    (mapped : RingHomRealization.mapAny phi (⟨n,f⟩ : AnySignature K)=
      ⟨2,NoXWeightedAntiSigned.anti v w⟩) :
    ∃ a b : K,phi a=v ∧ phi b=w ∧ (⟨n,f⟩ : AnySignature K)=⟨2,NoXWeightedAntiSigned.anti a b⟩ := by
  have hn : n=2 := congrArg Sigma.fst mapped
  subst n
  have hf : RingHomRealization.mapSignature phi f=NoXWeightedAntiSigned.anti v w :=
    eq_of_heq (Sigma.mk.inj_iff.mp mapped).2
  have hv : phi (f ![false,true])=v := by
    simpa [RingHomRealization.mapSignature,NoXWeightedAntiSigned.anti] using congrFun hf ![false,true]
  have hw : phi (f ![true,false])=w := by
    simpa [RingHomRealization.mapSignature,NoXWeightedAntiSigned.anti] using congrFun hf ![true,false]
  refine ⟨f ![false,true],f ![true,false],hv,hw,?_⟩
  apply congrArg (fun g : Signature K 2=>(⟨2,g⟩ : AnySignature K))
  funext x
  apply phi.injective
  have h := congrFun hf x
  change phi (f x)=_ at h
  refine h.trans ?_
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [NoXWeightedAntiSigned.anti,h0,h1,hv,hw]

variable (v w : D.K)
structure AntiRow where
  label : Fin (O.count G (data G D))
  left : O.field G (data G D)
  right : O.field G (data G D)
  left_value : (left : AlgebraicComplex)=(v : AlgebraicComplex)
  right_value : (right : AlgebraicComplex)=(w : AlgebraicComplex)
  literal : (⟨O.arity G (data G D) label.val,O.table G (data G D) label⟩ :
    AnySignature (O.field G (data G D)))=⟨2,NoXWeightedAntiSigned.anti left right⟩

def antiRow (i : Fin D.count)
    (literal : (⟨D.b i.val,D.H i⟩ : AnySignature D.K)=⟨2,NoXWeightedAntiSigned.anti v w⟩) :
    AntiRow G D v w := Classical.choice (by
  have member := old_member G D i
  change RingHomRealization.mapAny D.K.val.toRingHom (⟨D.b i.val,D.H i⟩ : AnySignature D.K)∈O.family G (data G D) at member
  rw [literal] at member
  have mapped : RingHomRealization.mapAny D.K.val.toRingHom (⟨2,NoXWeightedAntiSigned.anti v w⟩ : AnySignature D.K)=
      ⟨2,NoXWeightedAntiSigned.anti (v : AlgebraicComplex) (w : AlgebraicComplex)⟩ := by
    apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [RingHomRealization.mapSignature,NoXWeightedAntiSigned.anti,h0,h1]
  rw [mapped] at member
  obtain ⟨j,hj⟩ := member
  obtain ⟨v',w',hv,hw,he⟩ := lift_anti (O.field G (data G D)).subtype
    (O.table G (data G D) j) (v : AlgebraicComplex) (w : AlgebraicComplex) hj
  exact ⟨⟨j,v',w',hv,hw,he⟩⟩)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOrdinaryAnchorPins
end
