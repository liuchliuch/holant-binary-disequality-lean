import Holant.Proofs.Dichotomy.General.GenericOrdinarySource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin

/-! Preserve an existing genuine ordinary Eq4/pin source while adjoining
one actual labelled graph. The source field and final original oracle stay
unchanged, so recursive graph restrictions remain physical. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOrdinaryGraphSource
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace X
export NoXOrdinaryGraphAdjoin (Output arity signatures old old_literal newLabel new_literal source)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable {n : ℕ} (d : X.Output src.H n)

def data : GenericOrdinarySource.Data G where
  K := src.K
  degree := src.degree
  F := src.F
  size := src.size+1
  b := X.arity src.H d
  H := X.signatures src.F src.H d
  e := X.old src.H src.e
  p b := X.old src.H (src.p b)
  he := (X.old_literal src.F src.H d src.e).trans src.he
  hp b := (X.old_literal src.F src.H d (src.p b)).trans (src.hp b)
  toOriginal := Programme.compose (X.source src.F src.H d) src.toOriginal

theorem old_literal (i : Fin src.size) :
    (⟨(data G src d).b (X.old src.H i).val,(data G src d).H (X.old src.H i)⟩ : AnySignature src.K)=
      ⟨src.b i.val,src.H i⟩ := X.old_literal src.F src.H d i

theorem new_literal :
    (⟨(data G src d).b (X.newLabel src.H).val,(data G src d).H (X.newLabel src.H)⟩ : AnySignature src.K)=
      ⟨n,d.network.denote⟩ := X.new_literal src.F src.H d

theorem old_included : GenericOrdinarySource.family G src⊆GenericOrdinarySource.family G (data G src d) := by
  rintro f ⟨i,rfl⟩
  refine ⟨X.old src.H i,?_⟩
  exact congrArg (RingHomRealization.mapAny src.K.subtype) (old_literal G src d i)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOrdinaryGraphSource
end
