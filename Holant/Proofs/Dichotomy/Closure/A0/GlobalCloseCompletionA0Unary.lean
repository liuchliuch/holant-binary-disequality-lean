import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0DenseEscape
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0RowTransport
import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeUnary

/-! Saturate the actual original singular graph above the already sourced
q4-retained palette. Old R rows remain literal, so its actual scalar-X row is
carried into the enlargement. No marked group is assumed for the new palette. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Unary
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export GlobalCloseCompletionA0CurrentSource (retained)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (r : GlobalCloseCompletionA0DenseEscape.SingularReceipt G P torsion q core literal)

abbrev base := C.retained G P torsion q core literal

theorem old_base : P.family⊆(base G P torsion q core literal).family := by
  rw [ProgrammeRetained.palette_family]
  exact fullRetainedDeck_retains P.family torsion q

def root : AnySignature (OI.K G) := ⟨2,binarySignature r.original⟩
theorem root_nonzero : (root G P torsion q core literal r).2≠0 := by
  intro zero
  apply r.nonzero
  funext b d
  exact congrFun zero ![b,d]

theorem actual : Gadget.Realizes (base G P torsion q core literal).family .disequality
    (root G P torsion q core literal r).2 := r.actual.mono (old_base G P torsion q core literal)

def palette : Palette G := ProgrammeSaturation.palette G (base G P torsion q core literal)
  (root G P torsion q core literal r) (root_nonzero G P torsion q core literal r)
  (by change 0<2; decide) (actual G P torsion q core literal r)

theorem old : (base G P torsion q core literal).family⊆(palette G P torsion q core literal r).family :=
  ProgrammeSaturation.retains_old G (base G P torsion q core literal)
    (root G P torsion q core literal r) (root_nonzero G P torsion q core literal r)
    (by change 0<2; decide) (actual G P torsion q core literal r)

variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))

def row : GlobalCloseCompletionA0XSource.Row G (palette G P torsion q core literal r) :=
  GlobalCloseCompletionA0RowTransport.produce G (base G P torsion q core literal)
    (palette G P torsion q core literal r) (old G P torsion q core literal r)
    (GlobalCloseCompletionA0NativeCodec.actualRow G P torsion N q core literal)

def source := GlobalCloseCompletionA0NativeCodec.source G (palette G P torsion q core literal r)
  (row G P torsion q core literal r N)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Unary
end
