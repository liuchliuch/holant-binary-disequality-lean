import Holant.Proofs.Dichotomy.General.GenericOrdinarySource
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryXAdjoin

/-! Add literal X to an existing genuine Eq4/pin source using only its
actual ordinary scalar-X graph. All old rows and the original field remain. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GenericOrdinaryScalarXSource
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace X
export GlobalCloseCompletionOrdinaryXAdjoin (Output arity signatures old old_literal xLabel x_literal source)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (d : X.Output src.H)

def data : GenericLiteralXSource.Data G where
  K := src.K
  degree := src.degree
  F := src.F
  size := src.size+1
  b := X.arity src.H d
  H := X.signatures src.F src.H d
  e := X.old src.H src.e
  p b := X.old src.H (src.p b)
  x := X.xLabel src.H
  he := (X.old_literal src.F src.H d src.e).trans src.he
  hp b := (X.old_literal src.F src.H d (src.p b)).trans (src.hp b)
  hx := X.x_literal src.F src.H d
  toOriginal := Programme.compose (X.source src.F src.H d) src.toOriginal

theorem old_literal (i : Fin src.size) :
    (⟨(data G src d).b (X.old src.H i).val,(data G src d).H (X.old src.H i)⟩ : AnySignature src.K)=
      ⟨src.b i.val,src.H i⟩ := X.old_literal src.F src.H d i

theorem old_included : GenericOrdinarySource.family G src⊆GenericLiteralXSource.family G (data G src d) := by
  rintro f ⟨i,rfl⟩
  refine ⟨X.old src.H i,?_⟩
  exact congrArg (RingHomRealization.mapAny src.K.subtype) (old_literal G src d i)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GenericOrdinaryScalarXSource
end
