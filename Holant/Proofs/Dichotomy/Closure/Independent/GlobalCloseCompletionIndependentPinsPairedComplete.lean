import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsSource
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesAnchor
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTraceTerminal

/-! A genuine nonsingular interleaved paired quaternary closes an ordinary
two-pin source retaining trace-or-X provenance. The physical paired-series
Eq4 receipt, full old dictionary and original-G programme remain exact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsPairedComplete
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
namespace S
export GlobalCloseCompletionIndependentPinsSource (Data family)
end S
namespace U
export GlobalCloseCompletionUnaryDescentSource (ambient)
export GlobalCloseCompletionUnaryTraceOrX (Witness)
end U
namespace P
export GlobalCloseCompletionPairedSeriesCore (row)
export GlobalCloseCompletionPairedSeriesComplete (produce)
export GlobalCloseCompletionPairedSeriesReceipt (Receipt)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : S.Data G)
local instance : Algebra ℚ src.K:=src.K.algebra'
local instance : CharZero src.K:=Algebra.charZero_of_charZero ℚ src.K
variable (N : Macro src.H 4) (B : Matrix Bool Bool src.K)
variable (form : N.network.denote=P.row B) (det : B.det≠0)

def first : Macro src.H 1:=Macro.row (src.p false) (QuaternaryUnaryAccess.pin false) (src.hp false)
theorem first_zero : (first G src).network.denote (fun _=>false)=1 := by
  rw [first,Macro.row_denote]
  rfl
theorem first_one : (first G src).network.denote (fun _=>true)=0 := by
  rw [first,Macro.row_denote]
  rfl
def phi : src.K→+*ℂ := (algebraicClosure ℚ ℂ).subtype.comp src.K.subtype

def receipt : P.Receipt src.H src.F:=
  P.produce src.H src.F (phi G src) N B form det (first G src) 1 one_ne_zero
    (first_zero G src) (first_one G src)

abbrev anchor:=GlobalCloseCompletionPairedSeriesAnchor.input G src.K src.H src.F
  (receipt G src N B form det) src.toOriginal
abbrev data:=GlobalCloseCompletionOrdinaryAnchorPins.data G (anchor G src N B form det)

theorem receipt_old_included : S.family G src⊆U.ambient src.K (receipt G src N B form det).table := by
  rintro f ⟨i,rfl⟩
  exact ⟨(receipt G src N B form det).old i,
    congrArg (RingHomRealization.mapAny src.K.subtype) ((receipt G src N B form det).old_literal i)⟩

theorem old_included : S.family G src⊆GenericOrdinarySource.family G (data G src N B form det) :=
  (receipt_old_included G src N B form det).trans
    (GlobalCloseCompletionOrdinaryAnchorPins.old_included G (anchor G src N B form det))

include N B form det in
theorem classified (resource : U.Witness (S.family G src)) :
    Tract (S.family G src) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  have retained:=resource.mono (old_included G src N B form det)
  rcases GlobalCloseCompletionUnaryTraceTerminal.classified G (data G src N B form det) retained with positive|hard
  · exact Or.inl (positive.mono_family (old_included G src N B form det))
  · exact Or.inr hard

include N B form det in
theorem countingHard (resource : U.Witness (S.family G src)) (negative : ¬Tract (S.family G src)) :
    NoXWeightedAntiResourcesOriginal.Hard G :=
  (classified G src N B form det resource).resolve_left negative


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsPairedComplete
end
