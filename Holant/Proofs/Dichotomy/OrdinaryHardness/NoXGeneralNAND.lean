import Holant.Proofs.Dichotomy.General.GenericOrdinarySource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDMinorOriginal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiResourcesOriginal

/-! A literal unsigned NAND-support minor reaches the original counting
oracle from any actual ordinary Eq4/pin source. Row squaring supplies even
incidence, and the existing support interpolation is physically executed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralNAND
open Holant Holant.Algebraic Holant.Tractable Holant.Complexity Computability
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace O
export StableHigherCurrentOrdinarySquare (square)
export OrdinaryNegativeNANDMinorOriginal (square_pin)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (j : Fin src.size) (q : Fin (src.b j.val)→Bool ⊕ Fin 2)
variable (h00 : src.H j (T.substitute q ![false,false])≠0)
variable (h01 : src.H j (T.substitute q ![false,true])≠0)
variable (h10 : src.H j (T.substitute q ![true,false])≠0)
variable (h11 : src.H j (T.substitute q ![true,true])=0)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : PhysicalProgramme ea encodingNatBool
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding count (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (OrdinaryNegativeNANDMinorSource.source src.F (O.square src.H)
      j (src.p false) (src.p true) q
      (O.square_pin src.H (src.p false) false (src.hp false))
      (O.square_pin src.H (src.p true) true (src.hp true))
      (pow_ne_zero 2 h00) (pow_ne_zero 2 h01) (pow_ne_zero 2 h10)
      (by change (src.H j (T.substitute q ![true,true]))^2=0;rw [h11];simp) w)
    (GenericOrdinarySource.squareCSPSource G src).controlled)

include h00 h01 h10 h11 in
theorem countingHard : NoXWeightedAntiResourcesOriginal.Hard G := by
  intro α ea count w
  exact ⟨(source G src j q h00 h01 h10 h11 w).controlled.reduction⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralNAND
end
