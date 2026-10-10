import Holant.Proofs.Dichotomy.WithoutIdentity.NoISparseComplementAlgebra
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIActualEndpoint
import Holant.Proofs.Dichotomy.Native.NativeNormalizedGraphAdjoin

/-! One native-X-preserving common frame, an actual balanced q4 graph, and
an exact controlled source back to the unchanged original native oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementData
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
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
  basis : InvertibleKernel
  native : Kernel.pullback Signature.disequality basis.matrix=Signature.disequality
  retained : familyAction basis.symm (GlobalCloseCompletionUnaryDescentSource.ambient L H)⊆
    GlobalCloseCompletionUnaryDescentSource.ambient K table
  coeff : Fin 4→K
  first : coeff 0≠0
  graph : NativeAntiTargetSource.Output table 4
  form : graph.network.denote=GlobalCloseCompletionComplementQ4Series.row (coeff 0) (coeff 1) (coeff 2) (coeff 3)
  source : letI : Algebra ℚ K:=K.algebra';LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) presentation.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((NativeAntiTargetSource.base table presentation).evaluate presentation)
    ((NativeAntiTargetSource.base H F).evaluate F)
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementData
end
