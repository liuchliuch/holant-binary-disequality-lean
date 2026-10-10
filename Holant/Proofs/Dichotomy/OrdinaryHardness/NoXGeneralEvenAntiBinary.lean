import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenAntiBinarySource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiResourcesOriginal

/-! Original-oracle terminal for a bad binary even block and a full anti
even block. Neither block is assumed to be an ordinary binary gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiBinary
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (row antiRow : B.Block (s:=src.size) (b:=src.b) 2)
variable (v w : src.K) (hv : v≠0) (hw : w≠0)
variable (anti : antiRow.signature src.H=NoXWeightedAntiSigned.anti v w)
variable (nonaffine : ¬Affine (fun x=>(row.signature src.H x : AlgebraicComplex)))
variable (nonproduct : ¬Product (fun x=>(row.signature src.H x : AlgebraicComplex)))
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (wit : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (NoXGeneralEvenAntiBinarySource.source src.K src.F src.H src.e (src.p false) (src.p true)
      src.he (src.hp false) (src.hp true) row antiRow v w hv hw anti nonaffine nonproduct wit)
    src.toOriginal)

include hv hw anti nonaffine nonproduct in
theorem countingHard : NoXWeightedAntiResourcesOriginal.Hard G := by
  intro α ea count wit
  exact ⟨(source G src row antiRow v w hv hw anti nonaffine nonproduct wit).controlled.reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiBinary
end
