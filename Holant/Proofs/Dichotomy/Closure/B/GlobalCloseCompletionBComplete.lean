import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBNonisotropicResolved
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBResolved
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseResolved
import Holant.Proofs.Dichotomy.General.GenericLiteralXBSource

/-! Every actual exhausted B branch is consumed: higher, sparse, ordinary,
canonical dense and singular dense. The singular arm follows its same saved
pin and normalized phase through the actual cycle source. Only whole-current
tractability or genuine unchanged-original-G counting hardness remains. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBComplete
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export GlobalCloseCompletionBCurrent (palette Dense)
end B
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
variable (N : ClosureMarkedDihedralB.NativeB
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (B.palette G base R).family R.final.ready.torsion))
abbrev Hard := OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G
abbrev CurrentTract := GlobalCloseCompletionEq4Classification.CurrentTract G (B.palette G base R)

inductive Completion : Type 1 where
  | hard (proof : Hard G)
  | tract (criterion : CurrentTract G base R)

include N in
theorem singularContinuation (dense : B.Dense G base R)
    (receipt : GlobalCloseCompletionBDenseEscape.SingularReceipt G (B.palette G base R)) :
    CurrentTract G base R ∨ Hard G := by
  obtain ⟨o,four,p,full⟩ := dense
  let q := GeneratedGroupQ4Consumers.table G base four
  let core := GeneratedGroupQ4Consumers.minimum G base four
  have literal : core.signature=⟨4,q⟩ := GeneratedGroupQ4Consumers.minimum_literal G base four
  exact GlobalCloseCompletionBNonisotropicResolved.classified G (B.palette G base R)
    R.final.ready.torsion N receipt q p (literal ▸ core.retained) full

def complete : Completion G base R := Classical.choice (by
  cases GlobalCloseCompletionBResolved.complete G base R noPrior N with
  | hard proof => exact ⟨.hard proof⟩
  | tract criterion => exact ⟨.tract criterion⟩
  | singular dense receipt _unary =>
      rcases singularContinuation G base R N dense receipt with tract|hard
      · exact ⟨.tract tract⟩
      · exact ⟨.hard hard⟩)

include noPrior N in
theorem classified : CurrentTract G base R ∨ Hard G := by
  cases complete G base R noPrior N with
  | tract criterion => exact Or.inl criterion
  | hard proof => exact Or.inr proof

include base R noPrior N in
theorem inFP_or_countingHard :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ Hard G := by
  rcases classified G base R noPrior N with tract|hard
  · exact Or.inl (StablePaletteTractability.original_inFP G (B.palette G base R) tract)
  · exact Or.inr hard

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (B.palette G base R).family R.final.ready.torsion) : Type 1 := match M with
  | .bilinear _ => Completion G base R
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (B.palette G base R).family R.final.ready.torsion) : ForMarking G base R M := by
  cases M with
  | bilinear native => exact complete G base R noPrior native
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | monomial => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 := match result with
  | .initialStop .. => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) => forMarking G base exhausted rfl _

def original_current_bilinear_complete : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBComplete
end
