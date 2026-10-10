import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOnePair

/-! Actual paired two-point restrictions terminate at the unchanged original
G problem. Both selected retained rows, all literal X/pin factors, disjoint
private blocks, exact coefficient products and parity are explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXRankOnePairOriginal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
namespace E
export GenericLiteralXSource (count table arity xLabel pinLabel eq4Label
  x_literal pin_literal eq4_literal ordinarySource)
export GenericLiteralXSource (field presentation)
end E
namespace R
export OrdinaryNegativeRankOnePair (blocks row row_value row_nonaffine row_closed balanced source)
end R
namespace D
export OrdinaryNegativeMixedBlockData (EvenRecipe)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (j q : Fin (E.count G src))
variable (x₁ y₁ : Fin (E.arity G src j.val)→Bool)
variable (x₂ y₂ : Fin (E.arity G src q.val)→Bool)

def blocks := R.blocks (E.table G src) j q (E.xLabel G src) (E.pinLabel G src false)
  (E.pinLabel G src true) (E.x_literal G src) (E.pin_literal G src false)
  (E.pin_literal G src true) x₁ y₁ x₂ y₂

def row := R.row (E.table G src) j q (E.xLabel G src) (E.pinLabel G src false)
  (E.pinLabel G src true) (E.x_literal G src) (E.pin_literal G src false)
  (E.pin_literal G src true) x₁ y₁ x₂ y₂

theorem balanced (hd : Even (D.distance x₁ y₁+D.distance x₂ y₂)) :
    D.EvenRecipe (blocks G src j q x₁ y₁ x₂ y₂) :=
  R.balanced (E.table G src) j q (E.xLabel G src) (E.pinLabel G src false)
    (E.pinLabel G src true) (E.x_literal G src) (E.pin_literal G src false)
    (E.pin_literal G src true) x₁ y₁ x₂ y₂ hd

theorem row_value (z : Fin 1→Bool) : row G src j q x₁ y₁ x₂ y₂ z=
    if z 0 then E.table G src j y₁*E.table G src q y₂
      else E.table G src j x₁*E.table G src q x₂ :=
  R.row_value (E.table G src) j q (E.xLabel G src) (E.pinLabel G src false)
    (E.pinLabel G src true) (E.x_literal G src) (E.pin_literal G src false)
    (E.pin_literal G src true) x₁ y₁ x₂ y₂ z

variable (hleft : E.table G src j x₁*E.table G src q x₂≠0)
variable (hright : E.table G src j y₁*E.table G src q y₂≠0)
variable (bad : (E.table G src j x₁*E.table G src q x₂ : AlgebraicComplex)^4≠
  (E.table G src j y₁*E.table G src q y₂ : AlgebraicComplex)^4)

include hleft hright bad in
theorem row_nonaffine :
    ¬Affine (fun z=>(row G src j q x₁ y₁ x₂ y₂ z : AlgebraicComplex)) :=
  R.row_nonaffine (E.table G src) j q (E.xLabel G src) (E.pinLabel G src false)
    (E.pinLabel G src true) (E.x_literal G src) (E.pin_literal G src false)
    (E.pin_literal G src true) x₁ y₁ x₂ y₂ (E.field G src).subtype hleft hright bad

include hleft hright in
theorem row_closed :
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport.Closed
      (fun z=>(row G src j q x₁ y₁ x₂ y₂ z : AlgebraicComplex)) :=
  R.row_closed (E.table G src) j q (E.xLabel G src) (E.pinLabel G src false)
    (E.pinLabel G src true) (E.x_literal G src) (E.pin_literal G src false)
    (E.pin_literal G src true) x₁ y₁ x₂ y₂ (E.field G src).subtype hleft hright

/-- A real controlled source for the paired unary resource in original G. -/
def source (hd : Even (D.distance x₁ y₁+D.distance x₂ y₂)) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (R.source (E.table G src) j q (E.xLabel G src) (E.pinLabel G src false)
      (E.pinLabel G src true) (E.x_literal G src) (E.pin_literal G src false)
      (E.pin_literal G src true) x₁ y₁ x₂ y₂ (E.presentation G src)
      (E.eq4Label G src) (E.eq4_literal G src) hd)
    (E.ordinarySource G src))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXRankOnePairOriginal
end
