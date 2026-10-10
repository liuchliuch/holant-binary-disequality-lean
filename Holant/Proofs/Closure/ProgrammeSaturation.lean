import Holant.Proofs.Closure.RetainedFactorAdapters
import Holant.Proofs.Closure.InitialProgrammes
import Holant.Proofs.Closure.PhysicalPalette

/-! Genuine source-field saturated extension by one actual nonzero output.
Only the new output's tree is chosen; every old whole saved tree is copied.
The internally built source macros for all new exact slots are interpreted by
the existing controlled finite chain and charged at literal original-G codecs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeSaturation
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (q : AnySignature (OI.K G)) (nonzero : q.2 ≠ 0)

def controlledToOriginal (actual : Gadget.Realizes P.family .disequality q.2) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (RetainedFactorCatalogue.count G P q nonzero) 1
        (RetainedFactorCatalogue.arity G P q nonzero)) (OI.presentation G).encoding
      (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding
      (OriginalLCodec.value (RetainedFactorCatalogue.table G P q nonzero)) (OriginalForestSource.value G) :=
  InitialProgrammes.withTerminal (OI.presentation G)
    (Programme.compose (RetainedFactorCatalogue.toOld G P q nonzero) P.toOriginal.controlled)
    (RetainedFactorCatalogue.macroChain G P q nonzero actual)

def controlledFromOriginal : LengthControlledOracleReduction
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (RetainedFactorCatalogue.count G P q nonzero) 1
      (RetainedFactorCatalogue.arity G P q nonzero)) (OI.presentation G).encoding
    (OriginalForestSource.value G) (OriginalLCodec.value (RetainedFactorCatalogue.table G P q nonzero)) :=
  Programme.compose P.fromOriginal.controlled (RetainedFactorCatalogue.fromOld G P q nonzero)

def palette (positive : 0 < q.1) (actual : Gadget.Realizes P.family .disequality q.2) : Palette G :=
  RetainedFactorCatalogue.withPhysical G P q nonzero positive
    (PhysicalProgramme.ofControlled (controlledToOriginal G P q nonzero actual))
    (PhysicalProgramme.ofControlled (controlledFromOriginal G P q nonzero))

variable (positive : 0 < q.1) (actual : Gadget.Realizes P.family .disequality q.2)

@[simp] theorem family_exact : (palette G P q nonzero positive actual).family =
    RetainedFactorCatalogue.family G P q nonzero := rfl

theorem retains_old : P.family ⊆ (palette G P q nonzero positive actual).family := by
  rintro f ⟨i,rfl⟩
  exact RetainedFactorCatalogue.old_retained G P q nonzero i

theorem retains_output : q ∈ (palette G P q nonzero positive actual).family :=
  RetainedFactorCatalogue.root_retained G P q nonzero

/-- Whole tree equality includes its source signature, every stored split unit,
port bijection, and leaf constructor; duplicate tables remain separate labels. -/
theorem old_saved (i : Fin P.count) :
    let Q := palette G P q nonzero positive actual
    let j := RetainedFactorCatalogue.oldLabel G P q nonzero i
    (⟨⟨Q.arity j.val,Q.table j⟩,Q.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩ :=
  RetainedFactorCatalogue.old_saved G P q nonzero i

theorem root_saved :
    let Q := palette G P q nonzero positive actual
    let j := RetainedFactorCatalogue.rootLabel G P q nonzero
    (⟨⟨Q.arity j.val,Q.table j⟩,Q.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨q,RetainedFactorCatalogue.tree G q nonzero⟩ :=
  RetainedFactorCatalogue.root_saved G P q nonzero

theorem saturated : FactorSaturated (palette G P q nonzero positive actual).family :=
  Palette.saturated G (palette G P q nonzero positive actual)

@[simp] theorem toOriginal_controlled :
    (palette G P q nonzero positive actual).toOriginal.controlled =
      controlledToOriginal G P q nonzero actual := rfl

@[simp] theorem fromOriginal_controlled :
    (palette G P q nonzero positive actual).fromOriginal.controlled =
      controlledFromOriginal G P q nonzero := rfl

@[simp] theorem toOriginal_machine_and_clock :
    (palette G P q nonzero positive actual).toOriginal.controlled.reduction.machine =
      (controlledToOriginal G P q nonzero actual).reduction.machine ∧
    (palette G P q nonzero positive actual).toOriginal.controlled.reduction.time =
      (controlledToOriginal G P q nonzero actual).reduction.time := ⟨rfl,rfl⟩

@[simp] theorem fromOriginal_machine_and_clock :
    (palette G P q nonzero positive actual).fromOriginal.controlled.reduction.machine =
      (controlledFromOriginal G P q nonzero).reduction.machine ∧
    (palette G P q nonzero positive actual).fromOriginal.controlled.reduction.time =
      (controlledFromOriginal G P q nonzero).reduction.time := ⟨rfl,rfl⟩

def toOriginal_prefix_costs := Palette.toOriginal_prefix_costs G (palette G P q nonzero positive actual)
def fromOriginal_prefix_costs := Palette.fromOriginal_prefix_costs G (palette G P q nonzero positive actual)
def toOriginal_prefix_storage := Palette.toOriginal_prefix_storage G (palette G P q nonzero positive actual)
def fromOriginal_prefix_storage := Palette.fromOriginal_prefix_storage G (palette G P q nonzero positive actual)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeSaturation
