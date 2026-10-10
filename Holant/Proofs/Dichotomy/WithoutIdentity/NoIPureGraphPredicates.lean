import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareDataCore
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureUniformFour
import Holant.Tractable.Criteria
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant Holant.Tractable Holant.Algebraic
namespace NoIPureSquareGraphClosure
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'
def GraphFourthAffine : Prop:=∀n,∀N : NativeAntiTargetSource.Output D.table n,
  Affine (fun z=>(N.network.denote z : AlgebraicComplex)^4)
def GraphSquaredProduct : Prop:=∀n,∀N : NativeAntiTargetSource.Output D.table n,
  Product (fun z=>(N.network.denote z : AlgebraicComplex)^2)
end NoIPureSquareGraphClosure
namespace NoIPureSquareFour
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'
def GraphFour : Prop:=∀n,∀N : NativeAntiTargetSource.Output D.table n,NoIPureChargeTwoFamily.UniformFour N.network.denote

end NoIPureSquareFour
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1
end
