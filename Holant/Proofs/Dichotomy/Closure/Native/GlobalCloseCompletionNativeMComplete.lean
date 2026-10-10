import Holant.Proofs.Dichotomy.Closure.Native.GlobalCloseCompletionNativeMResolved
import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularResolved

/-! Unconditional classification of the actual exhausted native-M marking.
The final dense singular branch is consumed through its real Eq4 cycle and
unsigned NAND / actual X alternative. No ordinary or singular residual remains. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeMComplete
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionMixedCurrent
open GlobalCloseCompletionNativeMContinuation (CurrentTract)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion))
abbrev Hard := OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G

include noPrior N in
theorem classified : CurrentTract G base R ∨ Hard G := by
  cases GlobalCloseCompletionNativeMResolved.complete G base R noPrior N with
  | hard proof => exact Or.inr proof
  | tract criterion => exact Or.inl criterion
  | unary dense singular receipt =>
    obtain ⟨o,four,p,full⟩ := dense
    let q := GeneratedGroupQ4Consumers.table G base four
    let core := GeneratedGroupQ4Consumers.minimum G base four
    have literal : core.signature=⟨4,q⟩ := GeneratedGroupQ4Consumers.minimum_literal G base four
    exact GlobalCloseCompletionSingularResolved.classified G (palette G base R)
      R.final.ready.torsion N singular q p full
      (Gadget.realizes_of_mem (palette G base R).family .disequality _ (literal ▸ core.retained))

include base R noPrior N in
theorem inFP_or_countingHard :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ Hard G := by
  rcases classified G base R noPrior N with tract|hard
  · exact Or.inl (StablePaletteTractability.original_inFP G (palette G base R) tract)
  · exact Or.inr hard

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Prop :=
  match M with
  | .monomial _ => CurrentTract G base R ∨ Hard G
  | _ => True

include noPrior in
theorem forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | monomial native => exact classified G base R noPrior native
  | smallTwo => trivial
  | smallFour => trivial
  | cyclic => trivial
  | bilinear => trivial
  | unshifted => trivial
  | shifted => trivial
  | platonic => trivial

def ForResult (result : GeneratedGroupWorklist.Result G base) : Prop :=
  match result with
  | .initialStop .. => True
  | .prepared _ _ (.inl _) => True
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

theorem forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop .. => trivial
  | .prepared _ _ (.inl _) => trivial
  | .prepared _ _ (.inr exhausted) => forMarking G base exhausted rfl _

theorem original_current_nativeM_complete : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeMComplete
end
