import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedPortsCore

/-! Bind each minimal witness's original row, X and two pins to their actual
retained ordinary table labels, preserving exact sigma arities and values. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXUniversalLabels
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GenericLiteralXSource (count arity table xLabel pinLabel x_literal pin_literal)
export GenericLiteralXSource (field)
end E
namespace S
export OrdinaryNegativeSignedPortsCore (arity table)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (j : Fin (E.count G src))

def labels : Fin 4→Fin (E.count G src) := ![j,E.xLabel G src,E.pinLabel G src false,E.pinLabel G src true]

theorem literal (i : Fin 4) :
    (⟨E.arity G src (labels G src j i).val,E.table G src (labels G src j i)⟩ : AnySignature (E.field G src))=
      ⟨S.arity (E.arity G src j.val) i.val,S.table (E.table G src j) i⟩ := by
  fin_cases i
  · rfl
  · exact E.x_literal G src
  · exact E.pin_literal G src false
  · exact E.pin_literal G src true

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXUniversalLabels
end
