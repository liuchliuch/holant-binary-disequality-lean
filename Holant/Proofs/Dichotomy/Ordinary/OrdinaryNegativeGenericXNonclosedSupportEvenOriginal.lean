import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonclosedSupportEvenSource

/-! Any actual even private block over the Eq4 ordinary current table with nonclosed
support yields original-G counting hardness. All support witnesses, even row
copies, signed ports, finite binary gadgets and physical reductions are
constructed internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXNonclosedSupportEvenOriginal
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GenericLiteralXSource
  (count arity table eq4Label pinLabel xLabel eq4_literal pin_literal x_literal ordinarySource)
export GenericLiteralXSource (field presentation)
end S
namespace A
export OrdinaryNegativeNonclosedSupportEvenSource (source)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s n k : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (S.field G src) := (S.field G src).algebra'
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
variable (resource : D.Recipe (u:=1) (s:=S.count G src)
  (a:=fun _=>n+k) (b:=S.arity G src))
variable (nonclosed : ¬A.Closed (fun x=>(D.trace (S.table G src) k resource 0 x : AlgebraicComplex)))
variable (evenResource : D.EvenRecipe resource)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (A.source (S.field G src) (S.presentation G src) (S.table G src)
      resource nonclosed (S.xLabel G src) (S.pinLabel G src false)
      (S.x_literal G src) (S.pin_literal G src false)
      (S.eq4Label G src) (S.pinLabel G src true)
      (S.eq4_literal G src) (S.pin_literal G src true) evenResource w)
    (S.ordinarySource G src))

include nonclosed evenResource in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) := by
  intro α ea count w
  exact ⟨(source G src resource nonclosed evenResource w).controlled.reduction⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXNonclosedSupportEvenOriginal
end
