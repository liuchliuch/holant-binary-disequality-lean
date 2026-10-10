import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareData
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureAlphabetSource

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareAlphabet
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin s)→Signature L (a i.val)) (F : FixedField L degree)

def ofAlphabet (D : NoIPureAlphabetData.Data L H F) :
    NoIPureSquareData.Data (NoISuppliedIdentityConsumer.target L H F) where
  K:=D.K
  degree:=D.degree
  F:=D.presentation
  count:=D.count
  arity:=D.arity
  table:=D.table
  eq4:=D.equality
  pin:=D.pin
  x:=D.flip
  eq4_literal:=D.equality_literal
  pin_literal:=D.pin_literal
  x_literal:=D.flip_literal
  back:=D.source

def produce (pure : GlobalCloseCompletionComplementQ4ClassificationBlocks.Pure H) :
    NoIPureSquareData.Data (NoISuppliedIdentityConsumer.target L H F) :=
  ofAlphabet L H F (NoIPureAlphabetSource.produce L H F pure)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareAlphabet
end
