import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureRecipeCompression
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePairedHardCompanion

/-! Nonhardness consumes the actual independent paired nonProduct companion.
Every charge-zero recipe is therefore Affine, by its real graph source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureRecipeAffine
open Holant Holant.Tractable Holant.Algebraic
open scoped BigOperators
namespace R
export NoIPurePhaseRecipeFactor (Port word total)
end R
namespace T
export NoIPureRecipeTensor (output ports incidence word_value)
end T
namespace C
export NoIPureRecipeCompression (base location column_eq word_eq)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K := D.K.algebra'
variable (badP : ¬NoIPureProductPositive.WholeProduct target D)
variable (uniform : NoIPureSquareFour.GraphFour target D) (noHard : ¬target.Hard)
variable {k m : ℕ} {ns : Fin k → ℕ}
variable (N : (v : Fin k) → NativeAntiTargetSource.Output D.table (ns v))
variable (ps : (v : Fin k) → Fin (ns v) → R.Port m)
variable (legal : ∀ j, R.total ps j % 4 = 0)

include badP uniform noHard legal in
theorem affine : Affine (fun z => ∏ v, ((N v).network.denote (R.word (ps v) z) : AlgebraicComplex)) := by
  have h := NoIPurePairedHardCompanion.signed_affine target D badP uniform noHard
    (T.output D.table N) (C.base (T.ports ps)) (C.location (T.ports ps))
    (fun j => by rw [C.column_eq,T.incidence]; exact legal j)
  convert h using 1
  funext z
  rw [C.word_eq,T.word_value]
  exact (map_prod D.K.subtype _ _).symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureRecipeAffine
end
