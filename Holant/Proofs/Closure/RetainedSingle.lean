import Holant.Proofs.Closure.RetainedBranchAdapters
import Holant.Proofs.Closure.ProgrammeCompose
import Holant.Proofs.Closure.PhysicalCosts

/-! Closed source-backed physical access for one exact saved branch. Every
macro is physically composed into the returned finite original-G machine;
intermediate composite access is a separate, explicitly charged boundary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedBranch
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (q : AnySignature (OI.K G))

abbrev ToOriginalProgramme := PhysicalProgramme
  (RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P q)) (OI.presentation G).encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding
  (OriginalLCodec.value (extended G P q)) (OriginalForestSource.value G)

abbrev FromOriginalProgramme := PhysicalProgramme
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding
  (RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P q)) (OI.presentation G).encoding
  (OriginalForestSource.value G) (OriginalLCodec.value (extended G P q))

def controlledToOriginal (M : GeneralPowerExposure.PowerMacro P.table q.2) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P q)) (OI.presentation G).encoding
      (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding
      (OriginalLCodec.value (extended G P q)) (OriginalForestSource.value G) :=
  Programme.compose (controlledStep G P q M)
    (Programme.compose (oldToP G P q) P.toOriginal.controlled)

def controlledFromOriginal : LengthControlledOracleReduction
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (P.count+1) 1 (arity G P q)) (OI.presentation G).encoding
    (OriginalForestSource.value G) (OriginalLCodec.value (extended G P q)) :=
  Programme.compose P.fromOriginal.controlled (fromP G P q)

def toOriginal (M : GeneralPowerExposure.PowerMacro P.table q.2) : ToOriginalProgramme G P q :=
  PhysicalProgramme.ofControlled (controlledToOriginal G P q M)

def fromOriginal : FromOriginalProgramme G P q :=
  PhysicalProgramme.ofControlled (controlledFromOriginal G P q)

@[simp] theorem toOriginal_same_machine (M : GeneralPowerExposure.PowerMacro P.table q.2) :
    (toOriginal G P q M).controlled.reduction.machine =
      (controlledToOriginal G P q M).reduction.machine := rfl

@[simp] theorem fromOriginal_same_machine :
    (fromOriginal G P q).controlled.reduction.machine =
      (controlledFromOriginal G P q).reduction.machine := rfl


@[simp] theorem toOriginal_same_controlled (M : GeneralPowerExposure.PowerMacro P.table q.2) :
    (toOriginal G P q M).controlled = controlledToOriginal G P q M := rfl
@[simp] theorem fromOriginal_same_controlled :
    (fromOriginal G P q).controlled = controlledFromOriginal G P q := rfl
@[simp] theorem toOriginal_same_clock (M : GeneralPowerExposure.PowerMacro P.table q.2) :
    (toOriginal G P q M).controlled.reduction.time = (controlledToOriginal G P q M).reduction.time := rfl
@[simp] theorem fromOriginal_same_clock :
    (fromOriginal G P q).controlled.reduction.time = (controlledFromOriginal G P q).reduction.time := rfl

variable (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))


/-- Exact indexed-path version: the physical machine uses the macro obtained
by inspecting this same saved slot, with no existential re-selection of path. -/
def slotToOriginal (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (k : FullDeckIndex P.family torsion f)
    (j : Holant.LocalDrafts.Hardness.FactorSaturation.Slots (fullDeckRoot P.family torsion f k).2) :
    ToOriginalProgramme G P
      (Holant.LocalDrafts.Hardness.FactorSaturation.slot (fullDeckRoot P.family torsion f k).2 j).1 :=
  toOriginal G P _ (deckSlotPower G P torsion f core hcore k j)

/-- The macro and the original-G physical programme are constructed from
THIS exact key's exact stored subtree, rather than an independent leaf choice. -/
def subtreeToOriginal (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (k : FullDeckIndex P.family torsion f) (u : TreeOccurrence (OI.K G))
    (hu : Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule.StoredSubtree
      u (fullDeckRoot P.family torsion f k)) : ToOriginalProgramme G P u.1 :=
  toOriginal G P u.1 (deckSubtreePower G P torsion f core hcore k u hu)

/-- Literal retained inclusion supplies the original-to-branch direction;
it does not invent an uncharged query label. -/
def subtreeFromOriginal (u : TreeOccurrence (OI.K G)) : FromOriginalProgramme G P u.1 :=
  fromOriginal G P u.1

end Holant.LocalDrafts.RemoteWork.StableClosureV2.RetainedBranch
