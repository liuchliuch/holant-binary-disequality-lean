import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOnePair

/-! Actual paired two-point restrictions terminate at the unchanged original
G problem. Both selected retained rows, all literal X/pin factors, disjoint
private blocks, exact coefficient products and parity are explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOnePairOriginal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain
namespace E
export GlobalCloseCompletionEq4FullSource (count table arity xLabel pinLabel eq4Label
  x_literal pin_literal eq4_literal ordinarySource)
export GlobalCloseCompletionEq4CSPSource (field presentation)
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
variable (P : Palette G) (out : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (E.field G P out) := (E.field G P out).algebra'
variable (j q : Fin (E.count G P))
variable (x₁ y₁ : Fin (E.arity G P out j.val)→Bool)
variable (x₂ y₂ : Fin (E.arity G P out q.val)→Bool)

def blocks := R.blocks (E.table G P out) j q (E.xLabel G P) (E.pinLabel G P false)
  (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
  (E.pin_literal G P out true) x₁ y₁ x₂ y₂

def row := R.row (E.table G P out) j q (E.xLabel G P) (E.pinLabel G P false)
  (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
  (E.pin_literal G P out true) x₁ y₁ x₂ y₂

theorem balanced (hd : Even (D.distance x₁ y₁+D.distance x₂ y₂)) :
    D.EvenRecipe (blocks G P out j q x₁ y₁ x₂ y₂) :=
  R.balanced (E.table G P out) j q (E.xLabel G P) (E.pinLabel G P false)
    (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
    (E.pin_literal G P out true) x₁ y₁ x₂ y₂ hd

theorem row_value (z : Fin 1→Bool) : row G P out j q x₁ y₁ x₂ y₂ z=
    if z 0 then E.table G P out j y₁*E.table G P out q y₂
      else E.table G P out j x₁*E.table G P out q x₂ :=
  R.row_value (E.table G P out) j q (E.xLabel G P) (E.pinLabel G P false)
    (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
    (E.pin_literal G P out true) x₁ y₁ x₂ y₂ z

variable (hleft : E.table G P out j x₁*E.table G P out q x₂≠0)
variable (hright : E.table G P out j y₁*E.table G P out q y₂≠0)
variable (bad : (E.table G P out j x₁*E.table G P out q x₂ : AlgebraicComplex)^4≠
  (E.table G P out j y₁*E.table G P out q y₂ : AlgebraicComplex)^4)

include hleft hright bad in
theorem row_nonaffine :
    ¬Affine (fun z=>(row G P out j q x₁ y₁ x₂ y₂ z : AlgebraicComplex)) :=
  R.row_nonaffine (E.table G P out) j q (E.xLabel G P) (E.pinLabel G P false)
    (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
    (E.pin_literal G P out true) x₁ y₁ x₂ y₂ (E.field G P out).subtype hleft hright bad

include hleft hright in
theorem row_closed :
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport.Closed
      (fun z=>(row G P out j q x₁ y₁ x₂ y₂ z : AlgebraicComplex)) :=
  R.row_closed (E.table G P out) j q (E.xLabel G P) (E.pinLabel G P false)
    (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
    (E.pin_literal G P out true) x₁ y₁ x₂ y₂ (E.field G P out).subtype hleft hright

/-- A real controlled source for the paired unary resource in original G. -/
def source (hd : Even (D.distance x₁ y₁+D.distance x₂ y₂)) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (R.source (E.table G P out) j q (E.xLabel G P) (E.pinLabel G P false)
      (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
      (E.pin_literal G P out true) x₁ y₁ x₂ y₂ (E.presentation G P out)
      (E.eq4Label G P) (E.eq4_literal G P out) hd)
    (E.ordinarySource G P out))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOnePairOriginal
end
