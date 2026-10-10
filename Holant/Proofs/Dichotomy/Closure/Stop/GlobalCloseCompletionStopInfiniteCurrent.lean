import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopInfiniteUnary
import Holant.Proofs.Closure.GeneratedGroupWorklistExecution
import Holant.Proofs.Closure.InitialPalette

/-! Install the real two-unary programme at the same execution's infinite
stop, whether initial or reached after a genuine preparation history. Other
stop kinds and exhausted marked results retain their separate continuations.
The infinite arm is source access, not a claimed hardness classification. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteCurrent
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure hiding binarySignature
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace U
export GlobalCloseCompletionStopInfiniteUnary (inputEncoding presentation value physical)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

abbrev Access (B : Binary (K:=OI.K G)) (actual : ActualNonsingular P.family B)
    (infinite : ¬ProjectivelyFinite (transfer B)) :=
  PhysicalProgramme (U.inputEncoding G P) (U.presentation G P B actual infinite).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (U.value G P B actual infinite) (OriginalForestSource.value G)

def ForStop (stop : OccurrenceWorklist.Stop G P) : Type 1 :=
  match stop with
  | .infinite B actual infinite => Access G P B actual infinite
  | .unary .. => PUnit.{2}
  | .odd .. => PUnit.{2}

def forStop (stop : OccurrenceWorklist.Stop G P) : ForStop G P stop :=
  match stop with
  | .infinite B actual infinite => U.physical G P B actual infinite
  | .unary .. => PUnit.unit
  | .odd .. => PUnit.unit

variable (base : Palette G)

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 :=
  match result with
  | .initialStop stop _ => ForStop G base stop
  | .prepared _ _ (.inl stopped) => ForStop G stopped.finalSource.palette stopped.stop
  | .prepared _ _ (.inr _) => PUnit.{2}

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop stop _ => forStop G base stop
  | .prepared _ _ (.inl stopped) => forStop G stopped.finalSource.palette stopped.stop
  | .prepared _ _ (.inr _) => PUnit.unit

/-- Original G is the sole input; the binary, branch, spectral pencil, factors,
work fields and every actual graph/answer interpreter are produced internally. -/
def original_infinite_sources : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteCurrent
end
