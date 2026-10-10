import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXRankOnePairOriginal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXMixedBlockAffineXOriginal

/-! A family-level fourth-power conflict on parity-compatible word pairs,
together with an actual even nonproduct resource, has a complete counted
source in original G. The nonaffine unary, binary extraction and physical
sign compilation are all constructed internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXRankOnePairHardness
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GenericLiteralXSource (count arity table)
export GenericLiteralXSource (field)
end E
namespace R
export OrdinaryNegativeGenericXRankOnePairOriginal (blocks row_closed row_nonaffine balanced)
end R
namespace A
export OrdinaryNegativeGenericXMixedBlockAffineXOriginal (source)
end A
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance (distance)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s n k : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (j q : Fin (E.count G src))
variable (x₁ y₁ : Fin (E.arity G src j.val)→Bool)
variable (x₂ y₂ : Fin (E.arity G src q.val)→Bool)
variable (hd : Even (D.distance x₁ y₁+D.distance x₂ y₂))
variable (hleft : E.table G src j x₁*E.table G src q x₂≠0)
variable (hright : E.table G src j y₁*E.table G src q y₂≠0)
variable (bad : (E.table G src j x₁*E.table G src q x₂ : AlgebraicComplex)^4≠
  (E.table G src j y₁*E.table G src q y₂ : AlgebraicComplex)^4)
variable (second : D.Recipe (u:=1) (s:=E.count G src)
  (a:=fun _=>n+k) (b:=E.arity G src))
variable (hsecond : D.EvenRecipe second)
variable (hg : D.Closed (fun z=>(D.trace (E.table G src) k second 0 z : AlgebraicComplex)))
variable (hp : ¬Product (fun z=>(D.trace (E.table G src) k second 0 z : AlgebraicComplex)))
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  A.source G src (R.blocks G src j q x₁ y₁ x₂ y₂) second
    (R.row_closed G src j q x₁ y₁ x₂ y₂ hleft hright) hg
    (R.row_nonaffine G src j q x₁ y₁ x₂ y₂ hleft hright bad) hp
    (R.balanced G src j q x₁ y₁ x₂ y₂ hd) hsecond w

include hd hleft hright bad hsecond hg hp in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) := by
  intro α ea count w
  exact ⟨(source G src j q x₁ y₁ x₂ y₂ hd hleft hright bad second hsecond hg hp w).controlled.reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXRankOnePairHardness
end
