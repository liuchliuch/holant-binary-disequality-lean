import Holant.Proofs.Dichotomy.WithoutIdentity.NoISuppliedIdentityConsumer
import Holant.Proofs.Algorithms.QuaternaryUnaryAccess

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinsData
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)

structure Data : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  presentation : letI : Algebra ℚ K:=K.algebra';FixedField K degree
  count : ℕ
  arity : ℕ→ℕ
  table : (i : Fin count)→Signature K (arity i.val)
  retained : GlobalCloseCompletionUnaryDescentSource.ambient L H⊆
    GlobalCloseCompletionUnaryDescentSource.ambient K table
  pin : Bool→Fin count
  pin_literal : ∀b,(⟨arity (pin b).val,table (pin b)⟩ : AnySignature K)=⟨1,QuaternaryUnaryAccess.pin b⟩
  q : Signature K 4
  label : Fin count
  literal : (⟨arity label.val,table label⟩ : AnySignature K)=⟨4,q⟩
  pure : Holant.EightVertex.ProductAnchor.PureEquality (RingHomRealization.mapSignature K.subtype q)
  source : letI : Algebra ℚ K:=K.algebra';LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) presentation.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((NativeAntiTargetSource.base table presentation).evaluate presentation)
    ((NativeAntiTargetSource.base H F).evaluate F)

theorem lift_four {K : Type} [Field K] (phi : K→+*AlgebraicComplex) (f : AnySignature K)
    (q : Signature AlgebraicComplex 4) (h : RingHomRealization.mapAny phi f=⟨4,q⟩) :
    ∃g : Signature K 4,f=⟨4,g⟩ ∧ RingHomRealization.mapSignature phi g=q := by
  obtain ⟨n,f⟩:=f
  have hn : n=4:=congrArg Sigma.fst h
  subst n
  exact ⟨f,rfl,eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinsData
end
