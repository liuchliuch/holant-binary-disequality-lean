import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportSource

/-! Two actual even ordinary resources with affine supports and incompatible
A/P membership give original-G hardness. The complete tensor, support shifts,
private binary extraction, literal X compiler, and ordinary source composition
are internal; the caller supplies no binary gadget or hardness premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXMixedBlockAffineXOriginal
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GenericLiteralXSource
  (count arity table eq4Label pinLabel xLabel eq4_literal pin_literal x_literal ordinarySource)
export GenericLiteralXSource (field presentation)
end S
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace A
export OrdinaryNegativeAffineSupportSource (source)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s m n k l : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (S.field G src) := (S.field G src).algebra'
variable (first : D.Recipe (u:=1) (s:=S.count G src)
  (a:=fun _=>m+k) (b:=S.arity G src))
variable (second : D.Recipe (u:=1) (s:=S.count G src)
  (a:=fun _=>n+l) (b:=S.arity G src))
variable (hf : A.Closed (fun x=>(D.trace (S.table G src) k first 0 x : AlgebraicComplex)))
variable (hg : A.Closed (fun x=>(D.trace (S.table G src) l second 0 x : AlgebraicComplex)))
variable (ha : ¬Affine (fun x=>(D.trace (S.table G src) k first 0 x : AlgebraicComplex)))
variable (hp : ¬Product (fun x=>(D.trace (S.table G src) l second 0 x : AlgebraicComplex)))
variable (hfirst : D.EvenRecipe first) (hsecond : D.EvenRecipe second)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (A.source (S.field G src) (S.presentation G src) (S.table G src)
      first second hf hg ha hp (S.xLabel G src) (S.pinLabel G src false)
      (S.x_literal G src) (S.pin_literal G src false)
      (S.eq4Label G src) (S.pinLabel G src true)
      (S.eq4_literal G src) (S.pin_literal G src true) hfirst hsecond w)
    (S.ordinarySource G src))

include hf hg ha hp hfirst hsecond in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) := by
  intro α ea count w
  exact ⟨(source G src first second hf hg ha hp hfirst hsecond w).controlled.reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXMixedBlockAffineXOriginal
end
