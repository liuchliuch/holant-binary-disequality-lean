import Holant.Proofs.Closure.RetainedAdapters
import Holant.Proofs.Closure.InitialProgrammes
import Holant.Proofs.Closure.PhysicalPalette

/-! Reconstructed retained compiler. The real programme/palette factories are
preserved from an exact visible-read candidate; four returned-instance prefix
gates are reconstructed below and require fresh strict validation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeRetained
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)

/-- The actual finite internally constructed extraction chain is interpreted
at the current field's fixed basis and literal original-G terminal. -/
def controlledToOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (RetainedCatalogue.count G P torsion f) 1
      (RetainedCatalogue.arity G P torsion f)) (OI.presentation G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    (OriginalLCodec.value (RetainedCatalogue.table G P torsion f)) (OriginalForestSource.value G) :=
  InitialProgrammes.withTerminal (OI.presentation G)
    (Programme.compose (RetainedCatalogue.toOld G P torsion f) P.toOriginal.controlled)
    (RetainedCatalogue.macroChain G P torsion f core hcore)

/-- The old-label inclusion is an actual byte-preserving validated-input
programme, physically composed with the established original-G programme. -/
def controlledFromOriginal : LengthControlledOracleReduction
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    (RawClosedNetwork.validatedEncoding (RetainedCatalogue.count G P torsion f) 1
      (RetainedCatalogue.arity G P torsion f)) (OI.presentation G).encoding
    (OriginalForestSource.value G) (OriginalLCodec.value (RetainedCatalogue.table G P torsion f)) :=
  Programme.compose P.fromOriginal.controlled (RetainedCatalogue.fromOld G P torsion f)

/-- Both same-machine physical certificates, constructed rather than supplied. -/
def palette (hm : 2 ≤ m) : Palette G :=
  RetainedCatalogue.withPhysical G P torsion f hm
    (PhysicalProgramme.ofControlled (controlledToOriginal G P torsion f core hcore))
    (PhysicalProgramme.ofControlled (controlledFromOriginal G P torsion f))

@[simp] theorem palette_count (hm : 2 ≤ m) :
    (palette G P torsion f core hcore hm).count = RetainedCatalogue.count G P torsion f := rfl

@[simp] theorem palette_family (hm : 2 ≤ m) :
    (palette G P torsion f core hcore hm).family = fullRetainedDeck P.family torsion f :=
  RetainedCatalogue.family_exact G P torsion f

@[simp] theorem toOriginal_same_machine (hm : 2 ≤ m) :
    (palette G P torsion f core hcore hm).toOriginal.controlled.reduction.machine =
      (controlledToOriginal G P torsion f core hcore).reduction.machine := rfl

@[simp] theorem fromOriginal_same_machine (hm : 2 ≤ m) :
    (palette G P torsion f core hcore hm).fromOriginal.controlled.reduction.machine =
      (controlledFromOriginal G P torsion f).reduction.machine := rfl

/-- Reconstructed exact returned-instance cost gates. All original-G endpoint
encodings, actual machine/clock and every certified prefix are retained. -/
def toOriginal_prefix_costs (hm : 2 ≤ m) :=
  Palette.toOriginal_prefix_costs G (palette G P torsion f core hcore hm)

def fromOriginal_prefix_costs (hm : 2 ≤ m) :=
  Palette.fromOriginal_prefix_costs G (palette G P torsion f core hcore hm)

def toOriginal_prefix_storage (hm : 2 ≤ m) :=
  Palette.toOriginal_prefix_storage G (palette G P torsion f core hcore hm)

def fromOriginal_prefix_storage (hm : 2 ≤ m) :=
  Palette.fromOriginal_prefix_storage G (palette G P torsion f core hcore hm)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeRetained
