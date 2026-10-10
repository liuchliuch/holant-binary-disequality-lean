import Holant.Proofs.Dichotomy.General.GenericOrdinarySource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockBinarySource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiResourcesOriginal

/-! A genuine even private block with NAND support already supplies the
original counting oracle, without an antidiagonal or signed-variable oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenNAND
open Holant Holant.Algebraic Holant.Tractable Holant.Complexity Computability
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace B
export OrdinaryNegativeMixedBlockBinarySource (binary controlled)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s k : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (rows : D.Recipe (u:=1) (s:=src.size) (a:=fun _=>2+k) (b:=src.b))
variable (balanced : D.EvenRecipe rows)
variable (h00 : D.trace src.H k rows 0 ![false,false]≠0)
variable (h01 : D.trace src.H k rows 0 ![false,true]≠0)
variable (h10 : D.trace src.H k rows 0 ![true,false]≠0)
variable (h11 : D.trace src.H k rows 0 ![true,true]=0)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (Programme.compose (OrdinaryNegativeNANDSource.source src.F (B.binary src.H k rows)
      h00 h01 h10 h11 w)
      (B.controlled src.F src.H src.e (src.p false) (src.p true) src.he
        (src.hp false) (src.hp true) k rows balanced)) src.toOriginal)

include balanced h00 h01 h10 h11 in
theorem countingHard : NoXWeightedAntiResourcesOriginal.Hard G := by
  intro α ea count w
  exact ⟨(source G src rows balanced h00 h01 h10 h11 w).controlled.reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenNAND
end
