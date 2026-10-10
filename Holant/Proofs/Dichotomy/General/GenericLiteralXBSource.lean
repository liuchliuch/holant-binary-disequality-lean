import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityOriginal

/-! Instantiate the generic literal-X interface with the real B-normalized
Eq4/pin/X graph source.  The changed-coordinate table is never a Palette G;
its controlled graph programme is composed to unchanged original G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GenericLiteralXBSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export GlobalCloseCompletionBNativeCodec (mapped)
end C
namespace S
export GlobalCloseCompletionBEqualityCSP (field presentation arity table eq4Label pinLabel xLabel
  eq4_literal pin_literal x_literal)
end S
namespace O
export GlobalCloseCompletionBEqualityOriginal (ordinarySource family)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (d : GlobalCloseCompletionBPrimeEq4.Output (C.mapped G P))

def source : GenericLiteralXSource.Data G where
  K := S.field (C.mapped G P) d
  degree := _
  F := S.presentation (C.mapped G P) d
  size := _
  b := S.arity (C.mapped G P) d
  H := S.table (C.mapped G P) d
  e := S.eq4Label (C.mapped G P)
  p := S.pinLabel (C.mapped G P)
  x := S.xLabel (C.mapped G P)
  he := S.eq4_literal (C.mapped G P) d
  hp := S.pin_literal (C.mapped G P) d
  hx := S.x_literal (C.mapped G P) d
  toOriginal := O.ordinarySource G P d

@[simp] theorem family_exact : GenericLiteralXSource.family G (source G P d)=O.family G P d := rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GenericLiteralXBSource
end
