import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareDataCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareConsequences
import Holant.Proofs.Dichotomy.Native.NativeNormalizedGraphAdjoin

/-! Actual native Eq4/pin/X table with an explicit controlled old oracle.
Adjoining any genuine native graph retains the field, all old rows and the
same final programme, so squared-family consequences can apply to descendants. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareData
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace A
export NativeNormalizedGraphAdjoin (arity signatures old old_literal newLabel new_literal source)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target)


variable (D : Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'

def adjoin {n : ℕ} (N : NativeAntiTargetSource.Output D.table n) : Data target where
  K:=D.K
  degree:=D.degree
  F:=D.F
  count:=D.count+1
  arity:=A.arity D.table N
  table:=A.signatures D.F D.table N 1
  eq4:=A.old D.table D.eq4
  pin:=fun b=>A.old D.table (D.pin b)
  x:=A.old D.table D.x
  eq4_literal:=(A.old_literal D.F D.table N 1 D.eq4).trans D.eq4_literal
  pin_literal:=fun b=>(A.old_literal D.F D.table N 1 (D.pin b)).trans (D.pin_literal b)
  x_literal:=(A.old_literal D.F D.table N 1 D.x).trans D.x_literal
  back:=Programme.compose (A.source D.F D.table N 1 one_ne_zero) D.back

def label {n : ℕ} (N : NativeAntiTargetSource.Output D.table n) : Fin (adjoin target D N).count:=A.newLabel D.table

theorem literal {n : ℕ} (N : NativeAntiTargetSource.Output D.table n) :
    (⟨(adjoin target D N).arity (label target D N).val,(adjoin target D N).table (label target D N)⟩ : AnySignature D.K)=
      ⟨n,N.network.denote⟩ := by
  change (⟨A.arity D.table N (A.newLabel D.table).val,
    A.signatures D.F D.table N 1 (A.newLabel D.table)⟩ : AnySignature D.K)=⟨n,N.network.denote⟩
  simpa only [div_one] using A.new_literal D.F D.table N 1

theorem old_literal {n : ℕ} (N : NativeAntiTargetSource.Output D.table n) (i : Fin D.count) :
    (⟨(adjoin target D N).arity (A.old D.table i).val,(adjoin target D N).table (A.old D.table i)⟩ : AnySignature D.K)=
      ⟨D.arity i.val,D.table i⟩:=A.old_literal D.F D.table N 1 i


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareData
end
