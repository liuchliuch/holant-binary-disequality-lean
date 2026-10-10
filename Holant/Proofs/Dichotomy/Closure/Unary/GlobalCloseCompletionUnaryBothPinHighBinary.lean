import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinNormalized
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinProjection
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinLoops
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinPortChoice
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinBinaryPrime

/-! The high-rank binary UPF case contradicts actual minimality. Equal mask
bits are selected among outside ports before the ordinary loop is taken.
The semantic nonsmall loop is therefore a genuinely smaller physical graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinHighBinary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace D
export GlobalCloseCompletionUnaryBothPinNormalized (Data)
end D
namespace M
export GlobalCloseCompletionUnaryBothPinMinimal (arity small)
end M
namespace P
export GlobalCloseCompletionUnaryBothPinProjection (output dummy_small)
end P
namespace F
export GlobalCloseCompletionUnaryBitFlip (value tensorClosure)
export GlobalCloseCompletionUnaryBitFlipPins (cap_small_iff)
end F
namespace G
export GlobalCloseCompletionUnaryBothPinLoops (binaryOutput binaryMask binary_signed_denote)
end G
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature L (b i.val))
variable (pins : Bool→NoXOrdinaryGraphAdjoin.Output H 1)
variable (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
variable (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H))

include pinsForm negative in
theorem caps_small {n : ℕ} (positive : 0<n) (N : D.Data H (n+1))
    (bound : n<M.arity L H pins pinsForm negative) : ∀i : Fin (n+1),∀bit : Bool,
    Signature.TensorClosure (fun k (_ : Signature L k)=>k≤2)
      (fun z=>N.value (Function.update z i bit)) := by
  intro i bit
  apply (F.cap_small_iff N.mask N.actual.network.denote i bit).mpr
  apply P.dummy_small H pins pinsForm N.actual positive i (bit^^N.mask i)
  exact M.small L H pins pinsForm negative bound (P.output H pins N.actual i (bit^^N.mask i))

include pinsForm negative in
theorem impossible {t : ℕ} (positive : 0<t) (N : D.Data H (t+4))
    (size : t+4=M.arity L H pins pinsForm negative) (edge : I.minor N.value 0 1≠0) : False := by
  obtain ⟨e,e0,e1,same⟩:=GlobalCloseCompletionUnaryBothPinPortChoice.order positive N.mask
  let V:=N.reindex e
  have ev : I.minor V.value 0 1≠0 := by
    change I.minor (N.reindex e).value 0 1≠0
    rw [GlobalCloseCompletionUnaryBothPinNormalized.Data.reindex_minor,e0,e1]
    exact edge
  have tiny:=caps_small L H pins pinsForm negative (by omega : 0<t+3) V (by omega)
  have nonsmall:=GlobalCloseCompletionUnaryBothPinBinaryPrime.loop_not_small positive V.value
    V.value_prime V.origin ev tiny
  have physical:=M.small L H pins pinsForm negative (by omega : t+2<M.arity L H pins pinsForm negative)
    (G.binaryOutput H V.actual)
  have normalized:=F.tensorClosure (G.binaryMask V.mask) _ physical
  rw [G.binary_signed_denote H V.actual V.mask same] at normalized
  exact nonsmall normalized

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinHighBinary
end
