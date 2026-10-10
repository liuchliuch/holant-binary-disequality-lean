import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeCoordinateLiteral

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISuppliedIdentityData
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
variable {r degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin r)→Signature L (arity i.val)) (F : FixedField L degree)
structure Data : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  presentation : letI : Algebra ℚ K:=K.algebra';FixedField K degree
  count : ℕ
  b : ℕ→ℕ
  table : (i : Fin count)→Signature K (b i.val)
  identity : Fin count
  identity_literal : (⟨b identity.val,table identity⟩ : AnySignature K)=
    ⟨2,fun x=>Signature.equality (x 0) (x 1)⟩
  basis : InvertibleKernel
  native : Kernel.pullback Signature.disequality basis.matrix=Signature.disequality
  retained : familyAction basis.symm (GlobalCloseCompletionUnaryDescentSource.ambient L H)⊆
    GlobalCloseCompletionUnaryDescentSource.ambient K table
  source : letI : Algebra ℚ K:=K.algebra';LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) presentation.encoding
    (RawClosedNetwork.validatedEncoding r 1 arity) F.encoding
    ((NativeAntiTargetSource.base table presentation).evaluate presentation)
    ((NativeAntiTargetSource.base H F).evaluate F)
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISuppliedIdentityData
end
