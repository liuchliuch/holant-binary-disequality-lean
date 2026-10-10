import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankOneSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockAffineXOriginal

/-! An even-distance supported fourth-power failure supplies an actual
nonaffine unary. Together with an actual even closed-support nonproduct
resource, it yields counted hardness in the unchanged original G problem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneSingleHardness
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionEq4FullSource (count arity table xLabel pinLabel x_literal pin_literal)
export GlobalCloseCompletionEq4CSPSource (field)
end E
namespace R
export OrdinaryNegativeRankOneSource (originalBlocks originalRow row row_value row_nonaffine balanced)
end R
namespace A
export OrdinaryNegativeMixedBlockAffineXOriginal (source)
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

private theorem generic_closed {K : Type} [Field K] {s : ℕ} {b : ℕ→ℕ}
    (H : (j : Fin s)→Signature K (b j.val)) (j xLabel p₀ p₁ : Fin s)
    (hx : (⟨b xLabel.val,H xLabel⟩ : AnySignature K)=
      ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)
    (h₀ : (⟨b p₀.val,H p₀⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin false⟩)
    (h₁ : (⟨b p₁.val,H p₁⟩ : AnySignature K)=⟨1,OrdinaryNegativeRankOneCore.pin true⟩)
    (x y : Fin (b j.val)→Bool) (phi : K→+*AlgebraicComplex)
    (hleft : H j x≠0) (hright : H j y≠0) :
    D.Closed (fun z=>phi (R.row H j xLabel p₀ p₁ hx h₀ h₁ x y z)) := by
  intro u v w _ _ _
  apply (map_ne_zero phi).mpr
  rw [R.row_value]
  cases tripleXor u v w 0
  · exact hleft
  · exact hright

variable {s n k : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (out : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (E.field G P out) := (E.field G P out).algebra'
variable (j : Fin (E.count G P))
variable (x y : Fin (E.arity G P out j.val)→Bool)
variable (hleft : E.table G P out j x≠0) (hright : E.table G P out j y≠0)
variable (bad : (E.table G P out j x : AlgebraicComplex)^4≠
  (E.table G P out j y : AlgebraicComplex)^4)

include hleft hright in
theorem row_closed : D.Closed (fun z=>(R.originalRow G P out j x y z : AlgebraicComplex)) :=
  generic_closed (E.table G P out) j (E.xLabel G P) (E.pinLabel G P false)
    (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
    (E.pin_literal G P out true) x y (E.field G P out).subtype hleft hright

include hleft hright bad in
theorem row_nonaffine : ¬Affine (fun z=>(R.originalRow G P out j x y z : AlgebraicComplex)) :=
  R.row_nonaffine (E.table G P out) j (E.xLabel G P) (E.pinLabel G P false)
    (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
    (E.pin_literal G P out true) x y (E.field G P out).subtype hleft hright bad

variable (hd : Even (D.distance x y))
variable (second : D.Recipe (u:=1) (s:=E.count G P)
  (a:=fun _=>n+k) (b:=E.arity G P out))
variable (hsecond : D.EvenRecipe second)
variable (hg : D.Closed (fun z=>(D.trace (E.table G P out) k second 0 z : AlgebraicComplex)))
variable (hp : ¬Product (fun z=>(D.trace (E.table G P out) k second 0 z : AlgebraicComplex)))
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  A.source G P out (R.originalBlocks G P out j x y) second
    (row_closed G P out j x y hleft hright) hg
    (row_nonaffine G P out j x y hleft hright bad) hp
    (R.balanced (E.table G P out) j (E.xLabel G P) (E.pinLabel G P false)
      (E.pinLabel G P true) (E.x_literal G P out) (E.pin_literal G P out false)
      (E.pin_literal G P out true) x y hd) hsecond w

include hleft hright bad hd hsecond hg hp in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) := by
  intro α ea count w
  exact ⟨(source G P out j x y hleft hright bad hd second hsecond hg hp w).controlled.reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankOneSingleHardness
end
