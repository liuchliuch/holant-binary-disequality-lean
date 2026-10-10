import Holant.Proofs.Closure.ClosureCyclicCurrentBinaryPrime
import Holant.Proofs.Closure.ClosureCyclicCurrentPowerPalette

/-! The SAME extracted doubled outside factor becomes a real prime palette
label through its charged power macro. The base is the already saturated actual
square, so every old whole tree AND the square's once-saved tree stay exact.
This is actual installation/access, not old-P direct realizability. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) {m : ℕ}
variable (d : CyclicBoundary.NonsquareExit.DoubledOutside
  (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) m)

abbrev squareOriginal : AnySignature (OI.K G) := ⟨4,(doubledOutput G P d).output⟩
def squareNonzero : (squareOriginal G P d).2 ≠ 0 :=
  ProjectiveOutput.source_nonzero G P (doubledTensor G P d) (doubledOutput G P d) (doubledTensor_nonzero G P d)
def squareOldLabel (i : Fin P.count) : Fin (doubledPalette G P d).count :=
  RetainedFactorCatalogue.oldLabel G P (squareOriginal G P d) (squareNonzero G P d) i

def installedMacro : GeneralPowerExposure.PowerMacro (doubledPalette G P d).table (doubleFactors G P d).left :=
  ProgrammePowerTransport.relabel P.table (doubledPalette G P d).table
    (squareOldLabel G P d) (fun i => congrArg Sigma.fst
      (ProgrammeSaturation.old_saved G P (squareOriginal G P d) (squareNonzero G P d)
        (by norm_num) (doubledOutput G P d).source_actual i)) (doubleFactorPower G P d)

def installedPalette : Palette G := PowerPalette.palette G (doubledPalette G P d)
  ⟨2,(doubleFactors G P d).left⟩ (by norm_num) (doubleFactor_prime G P d) (installedMacro G P d)

def installedFactorLabel : Fin (installedPalette G P d).count :=
  PowerPalette.newLabel G (doubledPalette G P d)
def installedOldLabel (i : Fin P.count) : Fin (installedPalette G P d).count :=
  PowerPalette.oldLabel G (doubledPalette G P d) (squareOldLabel G P d i)
def installedSquareLabel : Fin (installedPalette G P d).count :=
  PowerPalette.oldLabel G (doubledPalette G P d)
    (RetainedFactorCatalogue.rootLabel G P (squareOriginal G P d) (squareNonzero G P d))

/-- The installed prime factor is literally the exact original split factor. -/
theorem installed_factor_saved :
    let Q := installedPalette G P d
    let i := installedFactorLabel G P d
    (⟨⟨Q.arity i.val,Q.table i⟩,Q.trees i⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨2,(doubleFactors G P d).left⟩,FactorTree.leaf _ (doubleFactor_prime G P d)⟩ :=
  PowerPalette.new_saved G (doubledPalette G P d) ⟨2,(doubleFactors G P d).left⟩ (doubleFactor_prime G P d)

theorem installed_old_saved (i : Fin P.count) :
    let Q := installedPalette G P d
    let j := installedOldLabel G P d i
    (⟨⟨Q.arity j.val,Q.table j⟩,Q.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩ :=
  (PowerPalette.old_saved G (doubledPalette G P d) ⟨2,(doubleFactors G P d).left⟩
    (doubleFactor_prime G P d) (squareOldLabel G P d i)).trans
    (ProgrammeSaturation.old_saved G P (squareOriginal G P d) (squareNonzero G P d)
      (by norm_num) (doubledOutput G P d).source_actual i)

/-- The once-selected square FactorTree is copied WHOLE, not regenerated after
its outside factor is installed as another label. -/
theorem installed_square_saved :
    let Q := installedPalette G P d
    let j := installedSquareLabel G P d
    (⟨⟨Q.arity j.val,Q.table j⟩,Q.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨squareOriginal G P d,RetainedFactorCatalogue.tree G (squareOriginal G P d) (squareNonzero G P d)⟩ :=
  (PowerPalette.old_saved G (doubledPalette G P d) ⟨2,(doubleFactors G P d).left⟩
    (doubleFactor_prime G P d) _).trans
    (ProgrammeSaturation.root_saved G P (squareOriginal G P d) (squareNonzero G P d)
      (by norm_num) (doubledOutput G P d).source_actual)

theorem installed_factor_retained : (⟨2,(doubleFactors G P d).left⟩ : AnySignature (OI.K G)) ∈
    (installedPalette G P d).family :=
  PowerPalette.retains_new G (doubledPalette G P d) _ (by norm_num) (doubleFactor_prime G P d) (installedMacro G P d)

theorem installed_factor_actual : ActualNonsingular (installedPalette G P d).family
    (binaryMatrix (doubleFactors G P d).left) :=
  retained_binary_prime_actual _ _ (installed_factor_retained G P d) (doubleFactor_prime G P d)

theorem installed_factor_outside : ¬CP.IsPhase m (CyclicBoundary.ActualCards.walshTransfer
    (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) (doubleFactors G P d).left)) :=
  doubleFactor_outside G P d

@[simp] theorem installed_toOriginal_controlled : (installedPalette G P d).toOriginal.controlled =
    RetainedBranch.controlledToOriginal G (doubledPalette G P d)
      ⟨2,(doubleFactors G P d).left⟩ (installedMacro G P d) := rfl
@[simp] theorem installed_fromOriginal_controlled : (installedPalette G P d).fromOriginal.controlled =
    RetainedBranch.controlledFromOriginal G (doubledPalette G P d) ⟨2,(doubleFactors G P d).left⟩ := rfl

def installed_toOriginal_prefix_costs := Palette.toOriginal_prefix_costs G (installedPalette G P d)
def installed_fromOriginal_prefix_costs := Palette.fromOriginal_prefix_costs G (installedPalette G P d)
def installed_toOriginal_prefix_storage := Palette.toOriginal_prefix_storage G (installedPalette G P d)
def installed_fromOriginal_prefix_storage := Palette.fromOriginal_prefix_storage G (installedPalette G P d)
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
